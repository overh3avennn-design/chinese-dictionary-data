#!/usr/bin/env python3
"""Порядок черт иероглифов для окна «Порядок черт» на странице «Словарь».

Что делает
    Берёт контуры и осевые линии черт из пакета hanzi-writer-data (данные
    проекта Make Me a Hanzi) и ключ каждого иероглифа из dictionary.txt того
    же проекта, добавляет русское название ключа (build/radicals-ru.tsv) и
    пишет по файлу на иероглиф:

        strokes/<код>.json   код — номер символа в Unicode, hex строчными:
                             你 → 4f60.json, 𠂇 → 20087.json

    Файл — объект в формате Hanzi Writer (сайт отдаёт его этой библиотеке
    как есть в режиме «Написать самому»), плюс ключ с названием:
        strokes     контуры черт по порядку, SVG-пути в квадрате 1024×1024
                    (ось y вверх, базовая линия на 900)
        medians     осевая линия каждой черты — по ней идёт анимация
        radStrokes  номера черт ключа (у ~550 иероглифов их нет)
        radical     [ключ, русское название], например ["亻", "человек"]
        layout      схема строения: ⿰ слева направо, ⿱ сверху вниз…
        parts       части: [[знак, [номера черт], название ключа?], …],
                    например 很 → [["彳", [0, 1, 2], "шаг"], ["艮", [3, …, 8], "упрямый"]];
                    знак "" — у части нет своего знака. Нет поля — иероглиф
                    на части не делится.

    Рядом кладёт тексты лицензий данных. Подробно — README.md.

Как запускать (из любой папки)
    python3 -I build/build_strokes.py --download   скачать исходники в source/strokes/ и собрать
    python3 -I build/build_strokes.py              собрать из уже скачанного

    Сборка переписывает только изменившиеся файлы, так что после правки
    названия ключа в radicals-ru.tsv в коммит попадут лишь затронутые
    иероглифы.
"""

import argparse
import io
import json
import os
import ssl
import sys
import tarfile
import urllib.request

BASE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SOURCE = os.path.join(BASE, "source", "strokes")
OUT = os.path.join(BASE, "strokes")
NAMES = os.path.join(BASE, "build", "radicals-ru.tsv")
SYSTEM_CA = "/etc/ssl/cert.pem"

HWD_VERSION = "2.0.1"
HWD_URL = f"https://registry.npmjs.org/hanzi-writer-data/-/hanzi-writer-data-{HWD_VERSION}.tgz"
MMAH_URL = "https://raw.githubusercontent.com/skishore/makemeahanzi/master/dictionary.txt"
# Текст LGPL 3.0 из набора SPDX: в нём же целиком GPL 3.0, на которую LGPL
# ссылается. gnu.org из-за VPN часто не отвечает, GitHub — отвечает.
LICENSES = {
    "LGPL-3.0.txt": "https://raw.githubusercontent.com/spdx/license-list-data/main/text/LGPL-3.0-or-later.txt",
}
# 阝 слева — 阜 «холм», справа — 邑 «город». Сторона — по средней x осевых
# линий черт ключа (квадрат 1024 в ширину).
FU_LEFT, FU_RIGHT = "холм", "город"


def get(url):
    ctx = ssl.create_default_context(cafile=SYSTEM_CA) if os.path.exists(SYSTEM_CA) else None
    with urllib.request.urlopen(url, context=ctx, timeout=120) as resp:
        return resp.read()


def download():
    os.makedirs(SOURCE, exist_ok=True)
    print("Скачиваю hanzi-writer-data", HWD_VERSION, "…", flush=True)
    data = get(HWD_URL)
    hwd = os.path.join(SOURCE, "hanzi-writer-data")
    os.makedirs(hwd, exist_ok=True)
    with tarfile.open(fileobj=io.BytesIO(data), mode="r:gz") as tar:
        for member in tar.getmembers():
            name = member.name.split("/", 1)[-1]
            # Только обычные файлы верхнего уровня пакета: JSON иероглифов и лицензия.
            if not member.isfile() or "/" in name or name == "package.json":
                continue
            if name.endswith(".json") or name == "ARPHICPL.TXT":
                with open(os.path.join(hwd, name), "wb") as f:
                    f.write(tar.extractfile(member).read())
    print("Скачиваю dictionary.txt Make Me a Hanzi …", flush=True)
    with open(os.path.join(SOURCE, "dictionary.txt"), "wb") as f:
        f.write(get(MMAH_URL))
    for name, url in LICENSES.items():
        with open(os.path.join(SOURCE, name), "wb") as f:
            f.write(get(url))


def load_names():
    names = {}
    with open(NAMES, encoding="utf-8") as f:
        for line in f:
            line = line.rstrip("\n")
            if not line.strip() or line.startswith("#"):
                continue
            form, name = line.split("\t")
            names[form] = name
    return names


def radical_name(form, names, char, data):
    if form != "阝":
        return names.get(form)
    rad = data.get("radStrokes") or []
    xs = [x for i in rad for x, _ in data["medians"][i]]
    if not xs:
        return f"{FU_LEFT} или {FU_RIGHT}"
    return FU_LEFT if sum(xs) / len(xs) < 512 else FU_RIGHT


# Описание строения иероглифа (IDS): оператор и его части, части бывают
# вложенными: 学 = ⿱⿱⺍冖子. Число частей у каждого оператора.
IDS_ARITY = {"⿰": 2, "⿱": 2, "⿲": 3, "⿳": 3, "⿴": 2, "⿵": 2, "⿶": 2, "⿷": 2,
             "⿸": 2, "⿹": 2, "⿺": 2, "⿻": 2}


def parse_ids(text, i=0):
    """Дерево IDS: строка-иероглиф («？» — часть без своего знака) или
    (оператор, [части]). Возвращает (узел, позиция после него)."""
    c = text[i]
    if c in IDS_ARITY:
        kids, i = [], i + 1
        for _ in range(IDS_ARITY[c]):
            kid, i = parse_ids(text, i)
            kids.append(kid)
        return (c, kids), i
    return c, i + 1


def split_parts(entry, data, names):
    """Части иероглифа для разбора: (схема, [[знак, [номера черт], название ключа?]…]).

    Части — составляющие верхнего уровня; если такая составляющая сама не
    иероглиф, а сборка из нескольких (学: ⿱⺍冖 сверху), берутся её части.
    Черты — по полю matches (путь каждой черты в дереве). Частей без черт не
    бывает; если осталось меньше двух — иероглиф на части не делится."""
    decomposition = entry.get("decomposition") or ""
    matches = entry.get("matches") or []
    try:
        tree, _ = parse_ids(decomposition)
    except IndexError:
        return None, []
    if not isinstance(tree, tuple):
        return None, []
    layout, kids = tree
    leaves = []                     # (путь, знак)
    for k, kid in enumerate(kids):
        if isinstance(kid, tuple):
            for j, sub in enumerate(kid[1]):
                leaves.append(((k, j), sub if isinstance(sub, str) else "？"))
        else:
            leaves.append(((k,), kid))
    parts = []
    for path, char in leaves:
        strokes = [s for s, m in enumerate(matches)
                   if m and tuple(m[:len(path)]) == path and s < len(data["strokes"])]
        if not strokes:
            continue
        part = ["" if char == "？" else char, strokes]
        name = None
        if char == "阝":
            name = radical_name(char, names, None, {"radStrokes": strokes, "medians": data["medians"]})
        elif char in names:
            name = names[char]
        if name:
            part.append(name)
        parts.append(part)
    if len(parts) < 2:
        return None, []
    return layout, parts


def write_if_changed(path, text):
    try:
        with open(path, encoding="utf-8") as f:
            if f.read() == text:
                return False
    except FileNotFoundError:
        pass
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        f.write(text)
    return True


def build():
    hwd = os.path.join(SOURCE, "hanzi-writer-data")
    if not os.path.isdir(hwd):
        sys.exit("Нет исходников в source/strokes/ — запустите с --download.")
    entries = {}
    with open(os.path.join(SOURCE, "dictionary.txt"), encoding="utf-8") as f:
        for line in f:
            entry = json.loads(line)
            entries[entry["character"]] = entry
    names = load_names()

    os.makedirs(OUT, exist_ok=True)
    chars = sorted(name[:-5] for name in os.listdir(hwd) if name.endswith(".json"))
    written, unnamed, keep, with_parts = 0, {}, set(), 0
    for char in chars:
        if len(char) != 1:
            continue
        with open(os.path.join(hwd, char + ".json"), encoding="utf-8") as f:
            data = json.load(f)
        out = {"strokes": data["strokes"], "medians": data["medians"]}
        if data.get("radStrokes"):
            out["radStrokes"] = data["radStrokes"]
        entry = entries.get(char, {})
        form = entry.get("radical")
        if form:
            name = radical_name(form, names, char, data)
            if name:
                out["radical"] = [form, name]
            else:
                unnamed[form] = unnamed.get(form, 0) + 1
        # Ключи (口, 木, 子…) — простые знаки: делить их на черточки (口 = 冂 + 一)
        # ученику только мешает.
        layout, parts = (None, []) if char in names else split_parts(entry, data, names)
        if parts:
            out["layout"] = layout
            out["parts"] = parts
            with_parts += 1
        file = f"{ord(char):x}.json"
        keep.add(file)
        text = json.dumps(out, ensure_ascii=False, separators=(",", ":")) + "\n"
        written += write_if_changed(os.path.join(OUT, file), text)

    # Иероглифы, пропавшие из исходников, удаляем.
    removed = 0
    for name in os.listdir(OUT):
        if name.endswith(".json") and name not in keep:
            os.remove(os.path.join(OUT, name))
            removed += 1
    for name in ("ARPHICPL.TXT",):
        with open(os.path.join(hwd, name), encoding="utf-8") as f:
            write_if_changed(os.path.join(OUT, name), f.read())
    for name in LICENSES:
        with open(os.path.join(SOURCE, name), encoding="utf-8") as f:
            write_if_changed(os.path.join(OUT, name), f.read())

    size = sum(os.path.getsize(os.path.join(OUT, n)) for n in keep)
    print(f"Иероглифов: {len(keep)}, {size / 1048576:.1f} МБ, "
          f"в среднем {size / len(keep) / 1024:.1f} КБ. С разбором на части: {with_parts}. "
          f"Изменено файлов: {written}, удалено: {removed}.")
    if unnamed:
        print("Нет названия в radicals-ru.tsv (ключ без названия не покажется):")
        for form, n in sorted(unnamed.items(), key=lambda x: -x[1]):
            print(f"  {form}  — {n} иероглифов")
        return 1
    return 0


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--download", action="store_true", help="скачать исходники в source/strokes/")
    args = ap.parse_args()
    if args.download:
        download()
    return build()


if __name__ == "__main__":
    sys.exit(main())
