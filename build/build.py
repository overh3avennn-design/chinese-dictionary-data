#!/usr/bin/env python3
"""Сборка словаря 大БКРС для страницы «Словарь» сайта chinese-learning-platform.

Что делает
    Читает ежедневную базу БКРС (dabkrs_*.gz со страницы https://dabkrs.com/p47,
    формат DSL) и раскладывает её на небольшие JSON-файлы. Страница словаря
    подгружает только те из них, что нужны для конкретного запроса:

        meta.json              версия базы и каталоги: в каком файле какой ключ
        v<версия>/e/<N>.json   статьи
        v<версия>/zh/<N>.json  индекс по иероглифам
        v<версия>/py/<N>.json  индекс по пиньиню (с тонами и без)
        v<версия>/ru/<N>.json  индекс по русским словам перевода

    В конце печатает размер всех данных и сколько загрузит первый поиск
    по нескольким примерам запросов. Подробно формат описан в README.md.

Как запускать (из любой папки)
    python3 -I build/build.py --download             скачать свежую базу в source/ и собрать
    python3 -I build/build.py source/dabkrs_261029.gz
    python3 -I build/build.py --report-only          только показать размер уже собранного

    Сборка занимает 6–7 минут и около 2,5 ГБ памяти. Старая папка
    v<версия>/ удаляется, meta.json переписывается последним — до этого
    момента сайт продолжает читать прежнюю версию.
"""

import argparse
import collections
import gzip
import json
import math
import os
import re
import shutil
import ssl
import sys
import time
import unicodedata
import urllib.parse
import urllib.request

BASE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SOURCE_DIR = os.path.join(BASE, "source")
HSK_WORDS = os.path.join(BASE, "build", "hsk-words.txt")

DOWNLOAD_PAGE = "https://dabkrs.com/p47"
USER_AGENT = "Mozilla/5.0 (chinese-dictionary-data build script)"
# Корневые сертификаты macOS: Python с python.org своих не видит.
SYSTEM_CA = "/etc/ssl/cert.pem"

# Файлы статей. Результаты одного запроса разбросаны по всему словарю, и
# на каждый приходится грузить целый файл, поэтому файлы мелкие: первые 10
# результатов — около 120 КБ в gzip, на мобильном интернете это 1–2 секунды.
# С файлами по 256 КБ было бы ~900 КБ.
ENTRY_KB = 32
# Файлы индексов: первый поиск грузит один такой файл.
INDEX_SHARD_KB = 48
# Сколько «частичных» результатов хранить для слова в индексе иероглифов
# (слова, в которые входит запрос) и пиньиня (слова, которые с него начинаются).
PARTIAL_TOP = 100
# Самый длинный кусок слова, по которому ищется «входит в слово».
CONTAINS_MAX = 8

VLQ_ALPHABET = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_"

# Служебные слова не попадают в индекс «слово встречается в переводе», но
# остаются в «точных» совпадениях: перевод «и» у 和 найдётся.
RU_STOPWORDS = set("""
а без бы был была были было быть в во вот все всё всего вы где да для до его
ее её ей ему если есть еще ещё же за и из или им их к как ко когда кого
который которая которое которые кто ли либо между мы на над не него нее неё
нет ни них но о об обо однако он она они оно от по под при про с со так также
там то тоже тот ты у уже чем что чтобы чьё чей эта эти это этот я
""".split())

CJK_RUN = re.compile("[\u3400-\u4dbf\u4e00-\u9fff\uf900-\ufaff\U00020000-\U0003134f]+")
CYRILLIC = re.compile("[а-яёА-ЯЁ]")
RU_WORD = re.compile("[а-яё]+")
PARENS = re.compile(r"\([^()]*\)")
GLOSS_SPLIT = re.compile(r"[;,:\n]")
NUMBERING = re.compile(r"^(?:\s*(?:\d+|[а-яa-z]|[ivx]+)[).]\s*)+")
GLOSS_STRIP = " .!?…-—–\"'«»“”„"
# Тег DSL ([m1], [/i], [c brown]), экранированный символ (\[) или текст.
DSL_TOKEN = re.compile(r"\\(.)|\[(/?)([a-z*]+)(\d*)(?: [^\]]*)?\]|([^\\\[]+)|(.)", re.S)
SPACES = re.compile(r"\s+")
EMPTY_MARK = re.compile(r"\[(p|i)\]\s*\[/\1\]")


def log(*args):
    print(*args, flush=True)


# ------------------------------------------------------------------ загрузка

def download(dest):
    """Скачивает сегодняшнюю базу dabkrs_*.gz в dest, возвращает путь к ней."""
    ctx = ssl.create_default_context(cafile=SYSTEM_CA) if os.path.exists(SYSTEM_CA) else None

    def get(url):
        req = urllib.request.Request(url, headers={"User-Agent": USER_AGENT})
        return urllib.request.urlopen(req, context=ctx, timeout=120)

    with get(DOWNLOAD_PAGE) as resp:
        page = resp.read().decode("utf-8", "replace")
    m = re.search(r"downloads/daily/(dabkrs_\d+\.gz)", page)
    if not m:
        sys.exit(f"На {DOWNLOAD_PAGE} не нашлась ссылка на dabkrs_*.gz — посмотрите страницу вручную.")
    os.makedirs(dest, exist_ok=True)
    path = os.path.join(dest, m.group(1))
    if os.path.exists(path):
        log(f"База уже скачана: {path}")
        return path
    url = urllib.parse.urljoin(DOWNLOAD_PAGE, m.group(0))
    log(f"Скачиваю {url}")
    part = path + ".part"
    with get(url) as resp, open(part, "wb") as f:
        shutil.copyfileobj(resp, f, 1 << 20)
    os.replace(part, path)
    return path


# --------------------------------------------------------------- разбор DSL

def read_dsl(path):
    """Отдаёт (заголовок, строка пиньиня, строка перевода) для каждой статьи.

    Статья в DSL — строка заголовка без отступа, под ней строки с отступом:
    первая — пиньинь («_», если его нет), дальше перевод. В паре статей
    перевод перенесён на следующую строку или перед пиньинем стоит лишняя
    строка, поэтому пиньинем считается строка прямо перед первой [m…]."""
    opener = gzip.open if path.endswith(".gz") else open
    with opener(path, "rt", encoding="utf-8-sig") as f:
        header = True
        block = []
        for line in f:
            line = line.rstrip("\r\n")
            if header:
                if line.startswith("#") or not line.strip():
                    continue
                header = False
            if not line.strip():
                if block:
                    yield split_block(block)
                    block = []
                continue
            block.append(line)
        if block:
            yield split_block(block)


def split_block(block):
    head = block[0].strip()
    rest = block[1:]
    first = next((i for i, line in enumerate(rest) if line.lstrip().startswith("[m")), None)
    if first is None:
        return head, rest[0].strip() if rest else "", " ".join(x.strip() for x in rest[1:])
    pinyin = rest[first - 1].strip() if first > 0 else ""
    return head, pinyin, " ".join(x.strip() for x in rest[first:])


class Cleaned:
    __slots__ = ("display", "index", "chinese")


def clean_dsl(text):
    """Разбирает перевод DSL.

    display — текст для страницы: строки [m…] через \\n, из тегов оставлены
              только [p]…[/p] (пометки: гл., см., уст.) и [i]…[/i] (курсивные
              комментарии), остальные теги убраны, их текст остаётся.
    index   — текст для индекса русских слов: без комментариев [i], пометок
              [p] и [c] и без примеров [ex].
    chinese — китайский текст из примеров [ex] и ссылок [ref]: по нему
              считается, насколько слово употребительно."""
    lines, index_lines, chinese = [], [], []
    cur, cur_index = [], []
    marks = []          # открытые в display [p]/[i]
    hidden = 0          # глубина тегов, текст которых не идёт в index
    quoted = 0          # глубина [ex]/[ref]

    def end_line():
        nonlocal hidden, quoted
        while marks:
            cur.append("[/" + marks.pop() + "]")
        line = EMPTY_MARK.sub("", EMPTY_MARK.sub("", SPACES.sub(" ", "".join(cur)))).strip()
        if line:
            lines.append(line)
        index_line = SPACES.sub(" ", "".join(cur_index)).strip()
        if index_line:
            index_lines.append(index_line)
        cur.clear()
        cur_index.clear()
        hidden = quoted = 0

    for m in DSL_TOKEN.finditer(text):
        escaped, slash, tag, _level, run, lone = m.groups()
        if tag is None:
            s = escaped if escaped is not None else (run if run is not None else lone)
            cur.append(s)
            if not hidden:
                cur_index.append(s)
            if quoted:
                chinese.append(s)
            continue
        closing = slash == "/"
        if tag == "m":
            end_line()
        elif tag in ("p", "i"):
            if closing:
                if tag in marks:
                    while marks:
                        t = marks.pop()
                        cur.append("[/" + t + "]")
                        if t == tag:
                            break
                hidden = max(0, hidden - 1)
            else:
                marks.append(tag)
                cur.append("[" + tag + "]")
                hidden += 1
        elif tag in ("c", "ex", "s", "com"):
            hidden = max(0, hidden - 1) if closing else hidden + 1
            if tag == "ex":
                quoted = max(0, quoted - 1) if closing else quoted + 1
        elif tag == "ref":
            quoted = max(0, quoted - 1) if closing else quoted + 1
        # b, *, u, sup, sub, lang, trn и прочие: тег убирается, текст остаётся.
    end_line()
    c = Cleaned()
    c.display = "\n".join(lines)
    c.index = "\n".join(index_lines)
    c.chinese = " ".join(chinese)
    return c


def clean_pinyin(raw):
    """Строка пиньиня для показа и для ключей индекса.

    В строке бывают несколько чтений через запятую и пометки вроде
    «[c][i]в сочет. также[/i][/c] huǐ» — в ключи они не попадают."""
    if raw in ("", "_"):
        return "", []
    c = clean_dsl(raw)
    display = c.display.replace("\n", " ")
    keys = []
    for reading in re.split(r"[,;/]", PARENS.sub(" ", c.index)):
        key = pinyin_key(reading)
        if key and key not in keys:
            keys.append(key)
    return display, keys


# ------------------------------------------------------------------ пиньинь

TONE_MARKS = {"\u0304": 1, "\u0301": 2, "\u030c": 3, "\u0300": 4}
VOWELS = set("aeiouv")


def pinyin_key(text):
    """«shuǐguǒ», «Shuǐ guǒ», «shui3guo3» → «shui3guo3».

    Знаки тона превращаются в цифру после слога, ü пишется v, лёгкий тон —
    без цифры, пробелы и апострофы убираются. Ту же функцию повторяет
    pinyinKey() на странице словаря — менять обе вместе.
    Возвращает "", если латинских букв в строке нет."""
    letters, tones, digits, breaks = [], [], {}, set()
    for ch in unicodedata.normalize("NFD", text.lower()):
        if "a" <= ch <= "z":
            letters.append(ch)
            tones.append(0)
        elif ch in TONE_MARKS:
            if letters:
                tones[-1] = TONE_MARKS[ch]
        elif ch == "\u0308" or ch == ":":
            if letters and letters[-1] == "u":
                letters[-1] = "v"
        elif "1" <= ch <= "5":
            if letters:
                digits[len(letters)] = int(ch)
            breaks.add(len(letters))
        else:
            breaks.add(len(letters))
    n = len(letters)

    def joined(i):
        """Буква i есть и стоит вплотную к предыдущей."""
        return i < n and i not in breaks

    last_end = 0
    for k in range(n):
        if not tones[k]:
            continue
        # Конец слога: после гласной со знаком — ещё одна i/o/u (ài, ào,
        # ǒu, huái), потом n или ng, если за ними не гласная. r входит в
        # слог только у самостоятельного er (èr, nǚ'ér); эризация (huàir,
        # wánr) остаётся хвостом без тона: huai4r, wan2r.
        j = k + 1
        if joined(j) and letters[j] in "iou" and not tones[j]:
            j += 1
        if joined(j):
            if letters[j] == "n":
                if joined(j + 1) and letters[j + 1] == "g" and not (joined(j + 2) and letters[j + 2] in VOWELS):
                    j += 2
                elif not (joined(j + 1) and letters[j + 1] in VOWELS):
                    j += 1
            elif (letters[j] == "r" and j == k + 1 and letters[k] == "e"
                  and (k == last_end or k in breaks)
                  and not (joined(j + 1) and letters[j + 1] in VOWELS)):
                j += 1
        digits.setdefault(j, tones[k])
        last_end = j
    out = []
    for i, ch in enumerate(letters):
        out.append(ch)
        tone = digits.get(i + 1)
        if tone and tone < 5:
            out.append(str(tone))
    return "".join(out)


def toneless(key):
    return re.sub(r"\d", "", key)


# ------------------------------------------------------- русские слова

def ru_norm(text):
    return text.lower().replace("ё", "е")


def russian_terms(index_text):
    """(главные, точные, остальные).

    Точные — слова, которые сами по себе составляют одно из значений
    перевода («1) вода»); главные — точные из первой строки с русским
    текстом, то есть из основного значения (爱 — «любить», а у 说 «любить»
    только в дальних значениях). Остальные — прочие слова перевода."""
    text = ru_norm(index_text)
    for _ in range(2):
        text = PARENS.sub(" ", text)
    main, exact = set(), set()
    first = True
    for line in text.split("\n"):
        if not RU_WORD.search(line):
            continue
        found = set()
        for gloss in GLOSS_SPLIT.split(line):
            gloss = NUMBERING.sub("", gloss).strip(GLOSS_STRIP)
            if gloss and RU_WORD.fullmatch(gloss):
                found.add(gloss)
        if first:
            main, first = found, False
        else:
            exact |= found
    words = set(w for w in RU_WORD.findall(text) if len(w) > 1 and w not in RU_STOPWORDS)
    exact -= main
    return tuple(main), tuple(exact), tuple(words - main - exact)


# ------------------------------------------------------- сжатие чисел

def vlq(numbers):
    """Возрастающий список чисел → строка: первое число и разности,
    каждое — группами по 5 бит, младшие вперёд; бит 32 — «дальше ещё»."""
    out = []
    prev = 0
    for n in numbers:
        d = n - prev
        prev = n
        while True:
            group = d & 31
            d >>= 5
            if d:
                out.append(VLQ_ALPHABET[group | 32])
            else:
                out.append(VLQ_ALPHABET[group])
                break
    return "".join(out)


def utf16_key(s):
    """Порядок строк как в JavaScript (по кодовым единицам UTF-16)."""
    return s.encode("utf-16-be")


def utf16_len(s):
    return len(s.encode("utf-16-le")) // 2


def common_prefix(a, b):
    """Общее начало двух ключей в единицах UTF-16, не больше 9 и не
    разрывая суррогатную пару."""
    n = 0
    for x, y in zip(a, b):
        if x != y:
            break
        step = 2 if ord(x) > 0xFFFF else 1
        if n + step > 9:
            break
        n += step
    return n


def prefix_chars(s, units):
    """Сколько символов Python занимают первые units единиц UTF-16."""
    i = n = 0
    while n < units:
        n += 2 if ord(s[i]) > 0xFFFF else 1
        i += 1
    return i


# ------------------------------------------------------------------ сборка

def load_hsk():
    levels = {}
    if os.path.exists(HSK_WORDS):
        with open(HSK_WORDS, encoding="utf-8") as f:
            for line in f:
                if line.startswith("#") or "\t" not in line:
                    continue
                word, level = line.rstrip("\n").split("\t")
                levels[word] = int(level)
    return levels


def build(source, out_dir):
    started = time.time()
    m = re.search(r"(\d{6})", os.path.basename(source))
    version = m.group(1) if m else time.strftime("%y%m%d")

    log(f"Читаю {source}")
    heads, pinyins, texts, py_keys, ru_terms, chinese = [], [], [], [], [], []
    for head, raw_pinyin, raw_text in read_dsl(source):
        c = clean_dsl(raw_text)
        p_display, p_keys = clean_pinyin(raw_pinyin)
        heads.append(head)
        pinyins.append(p_display)
        texts.append(c.display)
        py_keys.append(tuple(p_keys))
        ru_terms.append(russian_terms(c.index))
        chinese.append(c.chinese)
        if len(heads) % 500000 == 0:
            log(f"  {len(heads):,} статей · {time.time() - started:.0f} с")
    total = len(heads)
    log(f"  всего {total:,} статей")

    # Дальше номер статьи (ID) — её место в этом порядке.
    order, hsk_count = rank(heads, pinyins, texts, chinese)
    del chinese

    def reorder(items):
        return [items[old] for old in order]

    heads, pinyins, texts = reorder(heads), reorder(pinyins), reorder(texts)
    py_keys, ru_terms = reorder(py_keys), reorder(ru_terms)

    tmp = os.path.join(out_dir, f"v{version}.tmp")
    shutil.rmtree(tmp, ignore_errors=True)
    os.makedirs(tmp)

    log("Пишу статьи")
    entry_sizes = write_entries(tmp, heads, pinyins, texts)
    del texts

    log("Индекс иероглифов")
    zh_first = write_zh(tmp, heads)
    log("Индекс пиньиня")
    py_first = write_py(tmp, py_keys)
    del py_keys
    log("Индекс русских слов")
    ru_first = write_ru(tmp, ru_terms)
    del ru_terms

    final = os.path.join(out_dir, f"v{version}")
    shutil.rmtree(final, ignore_errors=True)
    os.rename(tmp, final)
    meta = {
        "name": "大БКРС",
        "source": "https://bkrs.info",
        "version": version,
        "count": total,
        # Статьи с ID меньше этого — слова HSK.
        "hsk": hsk_count,
        "base": f"v{version}/",
        "e": vlq(chunk_ends(entry_sizes)),
        "zh": zh_first,
        "py": py_first,
        "ru": ru_first,
    }
    write_json(os.path.join(out_dir, "meta.json.tmp"), meta)
    os.replace(os.path.join(out_dir, "meta.json.tmp"), os.path.join(out_dir, "meta.json"))
    for name in os.listdir(out_dir):
        if re.fullmatch(r"v\d{6}(\.tmp)?", name) and name != f"v{version}":
            shutil.rmtree(os.path.join(out_dir, name))
            log(f"Удалил старую версию {name}/")
    log(f"Готово за {time.time() - started:.0f} с")
    return heads


def chunk_ends(sizes):
    """Размеры файлов → номера первых статей следующих файлов (возрастающий
    ряд для vlq). Первый файл начинается с 0, его номер не храним."""
    out, n = [], 0
    for s in sizes:
        n += s
        out.append(n)
    return out


def rank(heads, pinyins, texts, chinese):
    """Порядок статей: сначала слова HSK (по уровню), потом остальные по
    оценке употребительности. От порядка зависит, какие результаты поиска
    показываются первыми и сколько файлов грузит первый поиск.
    Возвращает порядок и число слов HSK."""
    log("Считаю употребительность слов")
    position = {h: i for i, h in enumerate(heads)}
    # Сколько «основных» статей (с пиньинем — это ядро БКРС, а не
    # отраслевые термины) содержат слово как часть заголовка.
    inside = collections.Counter()
    for i, h in enumerate(heads):
        if not pinyins[i] or len(h) < 2:
            continue
        seen = set()
        for length in range(1, min(len(h) - 1, 4) + 1):
            for start in range(len(h) - length + 1):
                s = h[start:start + length]
                if s not in seen and s in position:
                    seen.add(s)
        inside.update(seen)
    # Сколько раз слово встречается в китайском тексте примеров и ссылок.
    used = collections.Counter()
    for text in chinese:
        if not text:
            continue
        for run in CJK_RUN.findall(text):
            for length in range(1, min(len(run), 4) + 1):
                for start in range(len(run) - length + 1):
                    s = run[start:start + length]
                    if s in position:
                        used[s] += 1
    hsk = load_hsk()
    scores = []
    for i, h in enumerate(heads):
        text = texts[i]
        score = (1.6 * math.log1p(inside[h]) + 1.2 * math.log1p(used[h])
                 + 1.0 * math.log1p(len(text))
                 + (2.5 if pinyins[i] else 0.0)
                 + (1.0 if CYRILLIC.search(text) else 0.0)
                 - 0.6 * max(0, len(h) - 2))
        if text.startswith("[p]см.[/p]") and "\n" not in text:
            score -= 1.5
        level = hsk.get(h)
        scores.append((0 if level else 1, level or 0, -score, i))
    scores.sort()
    return [s[3] for s in scores], sum(1 for s in scores if s[0] == 0)


def write_json(path, data):
    with open(path, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, separators=(",", ":"))


def json_size(item):
    return len(json.dumps(item, ensure_ascii=False, separators=(",", ":")).encode("utf-8")) + 1


def write_entries(out, heads, pinyins, texts):
    """Статьи по порядку ID: e/<N>.json — массив [иероглифы, пиньинь, перевод].
    Возвращает, сколько статей в каждом файле."""
    os.makedirs(os.path.join(out, "e"))
    sizes, chunk, chunk_bytes = [], [], 0
    for h, p, t in zip(heads, pinyins, texts):
        item = [h, p, t]
        size = json_size(item)
        if chunk and chunk_bytes + size > ENTRY_KB * 1024:
            write_json(os.path.join(out, "e", f"{len(sizes)}.json"), chunk)
            sizes.append(len(chunk))
            chunk, chunk_bytes = [], 0
        chunk.append(item)
        chunk_bytes += size
    if chunk:
        write_json(os.path.join(out, "e", f"{len(sizes)}.json"), chunk)
        sizes.append(len(chunk))
    log(f"  {len(sizes)} файлов")
    return sizes


def write_shards(out, name, records, group_of=None):
    """records — отсортированные (ключ, поля…). Каждая запись — строка
    «<общее начало с предыдущим ключом><остаток ключа>|поле|поле»; файл —
    массив таких строк. Возвращает первые ключи файлов (для meta.json).
    group_of(key) — граница файла не разрывает группу с одинаковым значением."""
    os.makedirs(os.path.join(out, name))
    firsts, shard, shard_bytes, prev = [], [], 0, ""
    group_prev = None

    def flush():
        write_json(os.path.join(out, name, f"{len(firsts) - 1}.json"), shard)

    for key, *fields in records:
        group = group_of(key) if group_of else key
        if shard and shard_bytes > INDEX_SHARD_KB * 1024 and group != group_prev:
            flush()
            shard, shard_bytes = [], 0
        if not shard:
            firsts.append(group)
            prev = ""
        lcp = common_prefix(prev, key)
        rec = str(lcp) + key[prefix_chars(key, lcp):]
        while fields and not fields[-1]:
            fields.pop()
        if fields:
            rec += "|" + "|".join(fields)
        shard.append(rec)
        shard_bytes += len(rec.encode("utf-8")) + 3
        prev = key
        group_prev = group
    if shard:
        flush()
    log(f"  {len(firsts)} файлов")
    return firsts


def write_zh(out, heads):
    """Индекс иероглифов: «заголовок|ID|ID слов, в которые он входит».

    Второй список — до PARTIAL_TOP самых важных статей, в заголовке которых
    есть это слово (学 → 学习, 大学, 学生…). Хранится только у заголовков,
    которые входят в другие заголовки."""
    position = {h: i for i, h in enumerate(heads)}
    contains = collections.defaultdict(list)
    for i, h in enumerate(heads):        # по порядку ID = по важности
        if len(h) < 2:
            continue
        seen = set()
        for length in range(1, min(len(h) - 1, CONTAINS_MAX) + 1):
            for start in range(len(h) - length + 1):
                s = h[start:start + length]
                if s in seen:
                    continue
                seen.add(s)
                if s in position:
                    lst = contains[s]
                    if len(lst) < PARTIAL_TOP:
                        lst.append(i)
    for h in heads:
        if "|" in h:
            raise SystemExit(f"В заголовке есть «|», формат индекса его не допускает: {h}")
    keys = sorted(position, key=utf16_key)
    records = ((h, vlq([position[h]]), vlq(contains.get(h, ()))) for h in keys)
    return write_shards(out, "zh", records)


def write_py(out, py_keys):
    """Индекс пиньиня: «ключ с тонами|ID: первое чтение|ID: другое чтение|
    ID слов, которые начинаются так же».

    Ключи отсортированы без учёта тонов (shi, shi1, shi2 … shiba1 …), так что
    все тона одного слога стоят рядом и в одном файле. «Первое чтение» —
    статьи, где это основное произношение (说 — shuō, а shuì — другое).
    Список «начинаются так же» — до PARTIAL_TOP самых важных статей, чей
    пиньинь без тонов длиннее и начинается с этого; он хранится у первой
    записи группы."""
    first = collections.defaultdict(list)
    other = collections.defaultdict(list)
    plain_ids = collections.defaultdict(list)
    for i, keys in enumerate(py_keys):
        seen = set()
        for n, k in enumerate(keys):
            (first if n == 0 else other)[k].append(i)
            t = toneless(k)
            if t not in seen:
                seen.add(t)
                plain_ids[t].append(i)
    # Для каждого пиньиня без тонов — статьи, чей пиньинь начинается с него.
    longer = collections.defaultdict(set)
    for t, ids in plain_ids.items():
        for n in range(1, len(t)):
            if t[:n] in plain_ids:
                longer[t[:n]].update(ids)
    keys = sorted(set(first) | set(other), key=lambda k: (utf16_key(toneless(k)), utf16_key(k)))
    records = []
    prev_plain = None
    for k in keys:
        t = toneless(k)
        ext = vlq(sorted(longer[t])[:PARTIAL_TOP]) if t != prev_plain and t in longer else ""
        prev_plain = t
        records.append((k, vlq(first.get(k, ())), vlq(other.get(k, ())), ext))
    return write_shards(out, "py", records, group_of=toneless)


def write_ru(out, ru_terms):
    """Индекс русских слов: «слово|ID главных|ID точных|ID остальных».

    Точные — статьи, где слово само по себе одно из значений («1) вода»),
    главные — где это значение первое (см. russian_terms), остальные — где
    слово просто встречается в переводе («минеральная вода»)."""
    lists = (collections.defaultdict(list), collections.defaultdict(list), collections.defaultdict(list))
    for i, terms in enumerate(ru_terms):
        for kind, words in zip(lists, terms):
            for w in words:
                kind[w].append(i)
    keys = sorted(set().union(*lists), key=utf16_key)
    records = ((w, *(vlq(kind.get(w, ())) for kind in lists)) for w in keys)
    return write_shards(out, "ru", records)


# ------------------------------------------------------------------ отчёт

def human(n):
    return f"{n / 1024 / 1024:,.1f} МБ" if n >= 1024 * 1024 else f"{n / 1024:,.0f} КБ"


def report(out_dir):
    with open(os.path.join(out_dir, "meta.json"), encoding="utf-8") as f:
        meta = json.load(f)
    root = os.path.join(out_dir, meta["base"])
    rows = []
    total = total_gz = files = 0
    biggest = 0
    for part, title in (("e", "статьи"), ("zh", "индекс иероглифов"),
                        ("py", "индекс пиньиня"), ("ru", "индекс русских слов")):
        size = size_gz = count = 0
        folder = os.path.join(root, part)
        for name in os.listdir(folder):
            path = os.path.join(folder, name)
            with open(path, "rb") as f:
                data = f.read()
            size += len(data)
            size_gz += len(gzip.compress(data, 6))
            biggest = max(biggest, len(data))
            count += 1
        rows.append((title, count, size, size_gz))
        total += size
        total_gz += size_gz
        files += count
    meta_size = os.path.getsize(os.path.join(out_dir, "meta.json"))
    log("")
    log(f"Словарь {meta['name']} v{meta['version']}: {meta['count']:,} статей")
    for title, count, size, size_gz in rows:
        log(f"  {title:<22} {count:>5} файлов  {human(size):>10}  (gzip {human(size_gz)})")
    log(f"  {'meta.json':<22} {1:>5} файл    {human(meta_size):>10}")
    log(f"  {'ИТОГО':<22} {files + 1:>5} файлов  {human(total + meta_size):>10}  (gzip {human(total_gz)})")
    log(f"  самый большой файл: {human(biggest)}")


def main():
    parser = argparse.ArgumentParser(description="Сборка словаря 大БКРС для сайта")
    parser.add_argument("source", nargs="?", help="файл dabkrs_*.gz (или распакованный .dsl)")
    parser.add_argument("--download", action="store_true", help="скачать свежую базу в source/")
    parser.add_argument("--out", default=BASE, help="куда писать (по умолчанию корень репозитория)")
    parser.add_argument("--report-only", action="store_true", help="только показать размер собранного")
    args = parser.parse_args()
    if not args.report_only:
        source = download(SOURCE_DIR) if args.download else args.source
        if not source:
            parser.error("укажите файл базы или --download")
        build(source, args.out)
    report(args.out)


if __name__ == "__main__":
    main()
