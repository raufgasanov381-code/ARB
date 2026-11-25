#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
ArbPhone — парсер вилок для Termux: Фонбет + Винлайн + БетБум, футбол, прематч -> Telegram.

Телефон сам качает линии БК, склеивает одинаковые матчи, ищет вилки
(1X2, тоталы, форы до ±1.5; опционально фрибет) и шлёт готовые вилки в Telegram.
Установка и запуск: см. README_termux.md.  Токен бота НЕ хранить в коде — только в config.json / env.
"""
import argparse
import base64
import calendar
import collections
import datetime as dt
import difflib
import gzip
import html as _html
import http.client
import hashlib
import hmac
import json
import math
import os
import random
import secrets
import shutil
import socket
import subprocess
import ssl
import re
import struct
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import uuid
import zlib

MSK = dt.timezone(dt.timedelta(hours=3))
UA = ("Mozilla/5.0 (Linux; Android 13; Pixel 7) AppleWebKit/537.36 (KHTML, like Gecko) "
      "Chrome/124.0 Mobile Safari/537.36")

DEFAULTS = {
    "bot_token": "",            # лучше через env ARB_BOT_TOKEN
    "chat_id": "",              # env ARB_CHAT_ID
    "node": "phone-1",
    "bank": 10000.0,            # банк для расчёта ставок, ₽
    "min_profit": 0.3,          # мин. профит денежной вилки, %
    "max_profit": 15.0,         # выше — считаем ошибкой данных и не шлём (между двумя БК бывает редко)
    "max_diverge": 0.45,        # макс. |ln(кф Винлайна / кф Фонбета)| на исход; больше — данные подозрительны
    "max_hcp_line": 2.5,        # форы только до этой линии (до 2.5 разбор сверен с Фонбетом, дальше мало данных)
    "interval": 60,             # период цикла, сек
    "max_age": 120,             # макс. разница во времени между снимками БК, сек
    "max_msgs": 8,              # максимум сообщений за цикл
    "dedup_ttl": 1200,          # не повторять ту же вилку, сек
    "corners": True,            # угловые (тотал, фора, 1-й тайм): страницы матчей Винлайна запрашиваются отдельно
    "corners_max": 30,          # сколько ближайших матчей с угловыми проверять за цикл
    "freebet_auto": True,       # присылать фрибетные вилки сами (иначе — только в меню)
    "freebet_bk": "",           # "fonbet" или "winline" — присылать только фрибет на этой БК (пусто = на обеих)
    "freebet_size": 0.0,        # размер фрибета для расчёта в меню (0 = 1000 ₽); на конверсию не влияет
    "min_conv": 10.0,           # мин. конверсия фрибета для списка в меню, %
    "min_conv_push": 70.0,      # мин. конверсия фрибета для автоотправки, %
    "open_access": True,        # любой, кто напишет боту /start, становится подписчиком
    "invite_code": "",          # если задан — вступить можно только по /start КОД
    "users_file": "",           # файл подписчиков (пусто = users.json рядом со скриптом)
    "fonbet_url": "https://line-vk-w.bk6bba-resources.ru/events/listBase?lang=ru&scopeMarket=1600",
    "winline_ws": "wss://wss.winline.ru/data_ng?client=newsite&nb=true",
    "betcity": True,            # Бетсити: футбол и другие виды спорта, прематч
    "betcity_ver": "97",        # параметры запросов сайта (из дампа браузера)
    "betcity_csn": "ooca9s",
    "betcity_hours": 48,        # матчи на ближайшие 24 / 48 / 72 часа
    "betcity_batch": 60,        # чемпионатов в одном запросе
    "betcity_threads": 1,
    "betcity_gap": 4.0,         # пауза между запросами к Бетсити, сек (при блокировке растёт сама до 12 с); при 2 с сайт обрывал соединения после ~6 запросов подряд
    "betcity_burst": 4,         # «ведро»: сколько запросов к Бетсити подряд можно
    "betcity_burst_start": 2,   # сколько запросов подряд разрешено сразу после запуска бота
    "betcity_per_min": 1.0,     # и сколько запросов в минуту в среднем (одна пачка в 40 секунд)
    "betcity_refresh": 900,     # как часто обновлять каждую пачку чемпионатов, сек
    "betcity_max_age": 1800,     # матчи старше этого (сек) не используются
    "betcity_champs_ttl": 1800, # как часто перечитывать список чемпионатов, сек
    "betcity_detail_ttl": 900,  # как долго хранить страницу матча (все линии), сек
    "betcity_detail_per_cycle": 3,   # сколько страниц матчей догружать за один цикл (запросов к Бетсити — как можно меньше)
    "betcity_curl": True,       # запросы Бетсити через системный curl (нужен pkg install curl; иначе встроенный Python)
    "betcity_budget": 50,       # максимум секунд на загрузку Бетсити за цикл (остальное — в следующих циклах)
    "betcity_ttl": 90,          # как часто обновлять список матчей Бетсити, сек (между обновлениями используется снимок)
    "betcity_detail_max": 80,   # для скольких ближайших совпавших матчей запрашивать все линии и угловые
    # Бетсити банит адрес на ~10 минут за частые запросы, поэтому по умолчанию только футбол; остальные виды можно добавить:
    # ["football", "hockey", "tennis", "basketball", "volleyball", "table-tennis", "handball", "futsal", "baseball", "rugby", "am-football", "floorball"]
    "betcity_sports": ["football", "hockey", "basketball", "tennis", "esports"],
    "leon": True,               # Леон: футбол и другие виды спорта, прематч
    "leon_ctag": "ru-RU-7da6p", # параметр запросов сайта (из дампа браузера)
    "leon_ver": "6.147.4",
    "leon_curl": True,
    "leon_threads": 4,
    "leon_max_leagues": 150,    # лиг на вид спорта (самые крупные первыми)
    "leon_budget": 120,         # максимум секунд на загрузку списка матчей Леона за цикл
    "leon_ttl": 90,             # как часто обновлять список матчей Леона, сек
    "leon_detail_max": 60,      # для скольких ближайших совпавших матчей запрашивать страницу (все линии, угловые, тайм)
    "leon_sports": ["football", "hockey", "tennis", "basketball", "volleyball", "table-tennis", "handball",
                    "futsal", "baseball", "rugby", "am-football", "floorball", "esports"],
    "horizon_hours": 48,        # брать только матчи, которые начнутся в ближайшие N часов (у всех БК); 0 — без ограничения
    "polymarket": True,         # Polymarket: открытый API (gamma), цены-вероятности -> коэффициенты с комиссией; ставки только в крипте
    "usd_rub": 0,               # курс доллара для сумм на Polymarket; 0 — брать курс ЦБ РФ автоматически
    "polymarket_ttl": 120,      # как часто обновлять список матчей, сек
    "polymarket_curl": True,
    "marathon": True,           # Марафон: HTML-страницы видов спорта, главные рынки (исход, двойной шанс, фора, тотал), без входа
    "marathon_sports": ["football", "hockey", "basketball", "tennis", "volleyball", "handball", "table-tennis", "futsal", "esports", "am-football", "baseball"],
    "marathon_ttl": 240,        # как часто обновлять Марафон, сек
    "marathon_gap": 1.0,        # пауза между запросами видов спорта, сек
    "marathon_tz": 3,           # часовой пояс времени на сайте Марафона (МСК = 3)
    "fb_rules": {},             # жёсткие правила фрибета (редко нужны): {"winline": {"min": 2.5, "vs": "fonbet", "vs_max": 3.0}}
    "role": "main",             # main — главный телефон (считает вилки, Telegram, сайт); worker — работник: опрашивает свои БК (bks) и выкладывает в репозиторий
    "worker_id": "",            # имя телефона-работника (tel2, ...)
    "bks": [],                  # БК, которые опрашивает работник: betcity, betboom, ligastavok, leon, olimp, marathon, onewin, polymarket
    "remote_bks": [],           # на главном телефоне: БК, которые всегда берутся у работников (обычно не нужно: см. auto_remote)
    "auto_remote": True,        # главный телефон сам берёт у работников БК, по которым есть свежие данные; умер работник — опрашивает БК сам
    "remote_max_age": 1200,     # данные работника старше этого (сек) не используются
    "worker_interval": 120,     # период цикла работника, сек
    "auto_update": None,        # автообновление кода из репозитория: у работника по умолчанию вкл, у главного выкл (true — включить)
    "update_every": 600,        # как часто проверять новую версию кода, сек
    "worker_fast_interval": 60, # как часто работник опрашивает Фонбет/Винлайн, сек
    "remote_fast_age": 420,     # сколько секунд данные Фонбета/Винлайна от работника считаются свежими
    "heartbeat_every": 240,     # как часто телефон обновляет свою карточку на сайте (модель, версия, статус), сек
    "keepalive": True,          # периодически открывать сайты Бетсити/БетБум/Лиги Ставок/Олимпа в браузере телефона (прогрев)
    "keepalive_every": 900,     # как часто, сек
    "bk_odds": {},              # границы коэффициента по БК для ФРИБЕТНЫХ вилок: {"winline": {"min": 1.3, "max": 2.5}}; меняется с сайта (settings.json)
    "bk_odds_cash": {},         # то же для ДЕНЕЖНЫХ вилок (по умолчанию любые коэффициенты); меняется с сайта
    "settings_poll": 30,        # как часто телефон проверяет настройки с сайта, сек
    "onewin": True,             # 1win: прематч через top-parser (список HTTP + коэффициенты socket.io), без входа
    "onewin_sports": ["football", "hockey", "basketball", "tennis", "volleyball", "table-tennis", "handball", "futsal", "am-football", "baseball", "esports"],
    "onewin_ttl": 240,          # как часто обновлять матчи и коэффициенты 1win, сек
    "onewin_max": 450,          # максимум матчей за цикл (ближайшие первыми)
    "onewin_per_sport": 300,    # матчей одного вида спорта (запросы по 100)
    "onewin_chunk": 13,         # матчей в одной подписке на коэффициенты
    "onewin_wait": 8,           # сколько секунд ждать ответ на одну подписку
    "olimp": True,              # Олимп: открытый API без входа, прематч, один запрос на вид спорта
    "olimp_sports": ["football", "hockey", "tennis", "basketball", "volleyball", "table-tennis", "handball", "baseball", "esports",
                     "am-football", "rugby", "waterpolo", "aussie-rules"],
    "olimp_gap": 2.5,           # пауза между запросами к Олимпу, сек
    "olimp_refresh": 600,       # как часто обновлять список матчей вида спорта, сек
    "olimp_refresh_football": 900,   # футбол — самый большой ответ (~1,4 МБ), поэтому реже
    "olimp_max_age": 1500,      # накопленные матчи старше этого (сек) не используются
    "olimp_budget": 90,         # максимум секунд на загрузку списков за цикл
    "olimp_detail_max": 40,     # для скольких ближайших совпавших матчей запрашивать страницу матча (все линии)
    "olimp_detail_per_cycle": 3,
    "olimp_detail_ttl": 600,
    "olimp_burst": 6,           # «ведро» запросов: сколько подряд можно
    "olimp_burst_start": 3,     # сколько сразу после запуска
    "olimp_per_min": 3.0,       # и сколько запросов в минуту в среднем
    "olimp_block_pause": 5400,  # пауза после блокировки адреса (Олимп закрыл доступ на 1,5 ч и дольше), сек
    "olimp_probe_pause": 1200,  # если после паузы доступа всё ещё нет — повторная проба через столько секунд
    "olimp_curl": True,
    "ligastavok": True,         # Лига Ставок: работает без входа в аккаунт (как гость, заголовки мобильного Chrome); выключить: "ligastavok": false
    "ls_anon": True,            # True — не использовать токены аккаунта (ls_headers в config.json игнорируются); False — использовать
    "ls_headers": {},           # заголовки x-api-cred / x-user из браузера, если сайт без них отвечает 401/403 (см. --ls-test)
    "ls_curl": True,
    "ls_gap": 2.0,              # пауза между запросами, сек (при ошибках растёт сама)
    "ls_limit": 40,             # матчей на страницу списка (сайт отдаёт максимум 40)
    "ls_max_events": 2000,      # максимум матчей на вид спорта
    "ls_max_age": 1200,         # накопленные матчи старше этого (сек) не используются
    "ls_budget": 90,            # максимум секунд на загрузку списка матчей за цикл (остальное — в следующих циклах)
    "ls_refresh": 420,          # как часто обновлять каждый вид спорта, сек
    "ls_detail_max": 80,        # для скольких ближайших совпавших матчей запрашивать страницу (все линии, тайм, угловые)
    "ls_detail_per_cycle": 8,   # сколько страниц матчей догружать за один цикл
    "ls_detail_ttl": 600,       # как долго хранить страницу матча, сек
    "ls_sports": ["football", "hockey", "tennis", "basketball", "volleyball", "table-tennis", "handball", "baseball", "esports",
                  "rugby", "am-football", "waterpolo"],
    "web_private": True,        # шифровать данные сайта: открыть их можно только личным кодом подписчика (выдаёт админ в Telegram)
    "web_url": "",              # адрес сайта для сообщений подписчикам; пусто — https://ЛОГИН.github.io/РЕПОЗИТОРИЙ/
    "web_repo": "",             # публикация вилок на сайт: "логин/репозиторий" на GitHub (публичный), см. README (раздел «Сайт»)
    "web_token": "",            # fine-grained токен GitHub: доступ только к этому репозиторию, Contents: Read and write
    "web_branch": "data",       # ветка с данными (создаётся сама), чтобы GitHub Pages не пересобирался от каждого обновления
    "web_every": 60,            # не чаще раза в N секунд
    "auto_warmup": True,        # при блокировке БК сам открыть её сайт в браузере телефона (termux-open-url) и повторить через warmup_wait сек
    "warmup_wait": 40,
    "warmup_every": 1800,       # не чаще раза в N секунд на БК
    "betboom": True,            # БетБум (Sporthub): футбол, прематч
    "betboom_ws": "wss://ru-ws.sporthub.bet/api/tree_ws/v1",
    "betboom_uuid": "01a0d23a-f305-719c-bb3d-11c5bed388f1",   # постоянный id браузера: случайный новый БетБум отклоняет (Access rejected)
    "betboom_chunk": 6,          # турниров на одно соединение (сервер отвечает лишь на первые ~5–6 подписок за соединение; 0 = одно соединение)
    "betboom_batch": 6,        # сколько турниров запрашивать одним кадром
    "betboom_timeout": 60,      # макс. ожидание ответов по турнирам, сек
    "betboom_detail_max": 40,   # для скольких ближайших совпавших матчей запрашивать страницу (ДШ, обе забьют, 1-й тайм, другие линии)
}

BB_UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) "
         "Chrome/152.0.0.0 YaBrowser/26.10.0.0 Safari/537.36")
BK_TITLE = {"fonbet": "Фонбет", "winline": "Винлайн", "betboom": "БетБум", "betcity": "Бетсити", "leon": "Леон", "ligastavok": "Лига Ставок", "olimp": "Олимп", "polymarket": "Polymarket", "onewin": "1win", "marathon": "Марафон"}
BKS = tuple(BK_TITLE)
FB_BKS = tuple(b for b in BKS if b != "polymarket")   # фрибетов у Polymarket нет
BK_IN = {"": "любой БК", "fonbet": "Фонбете", "winline": "Винлайне", "betboom": "БетБуме", "betcity": "Бетсити", "leon": "Леоне", "ligastavok": "Лиге Ставок", "olimp": "Олимпе", "polymarket": "Polymarket", "onewin": "1win", "marathon": "Марафоне"}


def log(*a):
    print(dt.datetime.now(MSK).strftime("%H:%M:%S"), *a, flush=True)


# ============================================================ конфиг

def _ls_import_token(cfg_path, cfg):
    """Если рядом со скриптом лежит ls_token.json (x-api-cred, x-user), записывает токены Лиги Ставок в config.json и переименовывает файл в .used."""
    tp = os.path.join(os.path.dirname(os.path.abspath(__file__)), "ls_token.json")
    if not os.path.exists(tp):
        return
    try:
        with open(tp, encoding="utf-8") as fh:
            t = json.load(fh)
        if len(t.get("x-api-cred", "")) < 50 or not t.get("x-user"):
            return
        c = {}
        if os.path.exists(cfg_path):
            with open(cfg_path, encoding="utf-8") as fh:
                c = json.load(fh)
        hh = dict(c.get("ls_headers") or {})
        hh["x-api-cred"], hh["x-user"] = t["x-api-cred"], t["x-user"]
        c["ls_headers"] = hh
        c["ligastavok"] = True
        c["ls_token_saved"] = int(t.get("saved") or time.time())
        with open(cfg_path, "w", encoding="utf-8") as fh:
            json.dump(c, fh, ensure_ascii=False, indent=2)
        os.replace(tp, tp + ".used")
        cfg["ls_headers"], cfg["ligastavok"], cfg["ls_token_saved"] = hh, True, c["ls_token_saved"]
        print("Токены Лиги Ставок взяты из ls_token.json и записаны в config.json", flush=True)
    except Exception as e:
        print("ls_token.json не обработан: %s" % e, flush=True)


def load_cfg(path):
    cfg = dict(DEFAULTS)
    p = path or os.path.join(os.path.dirname(os.path.abspath(__file__)), "config.json")
    if os.path.exists(p):
        with open(p, encoding="utf-8") as fh:
            cfg.update(json.load(fh))
    _ls_import_token(p, cfg)
    if os.environ.get("ARB_BOT_TOKEN"):
        cfg["bot_token"] = os.environ["ARB_BOT_TOKEN"]
    if os.environ.get("ARB_CHAT_ID"):
        cfg["chat_id"] = os.environ["ARB_CHAT_ID"]
    if os.environ.get("ARB_INVITE_CODE"):
        cfg["invite_code"] = os.environ["ARB_INVITE_CODE"]
    return cfg


# ============================================================ сеть

def http_get(url, headers, timeout=40):
    req = urllib.request.Request(url, headers=headers)
    with urllib.request.urlopen(req, timeout=timeout) as r:
        raw = r.read()
        if (r.headers.get("Content-Encoding") or "").lower() == "gzip":
            raw = gzip.decompress(raw)
    return raw


def fonbet_fetch(cfg):
    raw = http_get(cfg["fonbet_url"], {
        "User-Agent": UA, "Accept": "*/*", "Accept-Encoding": "gzip",
        "Accept-Language": "ru,en;q=0.9", "Origin": "https://fon.bet", "Referer": "https://fon.bet/",
    })
    return json.loads(raw)


def _gunzip(b):
    try:
        return gzip.decompress(b)
    except Exception:
        return None


def winline_fetch(cfg, timeout=18):
    """Подключается к WebSocket Винлайна, шлёт 5 стартовых кадров (как браузер) и забирает каталог линии."""
    try:
        import websocket  # pip install websocket-client
    except ImportError:
        sys.exit("Нужен пакет: pip install websocket-client")
    ws = websocket.create_connection(
        cfg["winline_ws"], timeout=10, origin="https://winline.ru",
        header=["User-Agent: " + UA, "Accept-Language: ru,en;q=0.9"])
    msgs = []
    try:
        for frame in ("lang", "AA==", "data", "WINLINE", "getdate"):
            ws.send(frame)
        ws.settimeout(2.5)
        end = time.time() + timeout
        big = False
        while time.time() < end:
            try:
                op, data = ws.recv_data()
            except websocket.WebSocketTimeoutException:
                if big:
                    break
                continue
            if op == websocket.ABNF.OPCODE_CLOSE:
                break
            if op == websocket.ABNF.OPCODE_BINARY:
                raw = _gunzip(data)
                if raw:
                    msgs.append(raw)
                    if len(raw) > 200_000:
                        big = True
    finally:
        try:
            ws.close()
        except Exception:
            pass
    return msgs


def parse_detail(frame):
    """Кадр страницы матча (ответ на event.plus) -> (id события, [(id записи, код, флаг, линия, [коэффициенты])])."""
    if len(frame) < 16:
        return None
    eid = struct.unpack_from("<I", frame, 2)[0]
    pos = [m.start() for m in re.finditer(rb"\x10\x27\x10\x27", frame)]
    out = []
    for k, p in enumerate(pos):
        if p < 6:
            continue
        rid, code = struct.unpack_from("<IH", frame, p - 6)
        end = pos[k + 1] - 6 if k + 1 < len(pos) else len(frame)
        b = frame[p + 4:end]
        try:
            flag, sl = b[0], _u16(b, 1)
            line = b[3:3 + sl].decode("utf-8", "replace")
            o = 3 + sl
            n = struct.unpack_from("<I", b, o)[0]
            if not 0 < n <= 12 or len(b) < o + 4 + 4 * n:
                continue
            odds = [struct.unpack_from("<I", b, o + 4 + 4 * j)[0] / 10000.0 for j in range(n)]
        except Exception:
            continue
        out.append((rid, code, flag, line, odds))
    return eid, out


def corner_markets(recs):
    """Записи страницы матча Винлайна -> рынки угловых (сверено с Фонбетом по матчу Азербайджан U19 – Черногория U19):
    1070 тотал угловых, 1079 фора угловых, 1006 тотал угловых 1-го тайма, 1010 фора угловых 1-го тайма
    (флаг фор: 0 ноль, 1 минус у хозяев, 2 плюс у хозяев; кф: хозяева, гости)."""
    mk = {}
    for _rid, code, flag, line, odds in recs:
        if len(odds) != 2 or min(odds) <= 1.0:
            continue
        try:
            L = float(line)
        except ValueError:
            continue
        if (L * 2) != int(L * 2):
            continue
        if code in (1070, 1006):
            mk.setdefault(("" if code == 1070 else "1H:") + "CRN:TOTAL:%.2f" % L, {"O": odds[0], "U": odds[1]})
        elif code in (1079, 1010) and flag in (0, 1, 2):
            hl = 0.0 if flag == 0 else (-L if flag == 1 else L)
            mk.setdefault(("" if code == 1079 else "1H:") + "CRN:HCP:%.2f" % (hl + 0.0), {"1": odds[0], "2": odds[1]})
    return mk


def winline_details(cfg, wids, timeout=45):
    """Открывает сессию, дожидается каталога и по очереди запрашивает страницы матчей (event.plus + id),
    как это делает браузер: следующий запрос — после ответа на предыдущий. -> {id: записи}"""
    import base64
    try:
        import websocket
    except ImportError:
        sys.exit("Нужен пакет: pip install websocket-client")
    ws = websocket.create_connection(cfg["winline_ws"], timeout=10, origin="https://winline.ru",
                                     header=["User-Agent: " + UA, "Accept-Language: ru,en;q=0.9"])
    got, frames, other = {}, 0, set()
    deadline = time.time() + timeout

    def pump(wait, until=None):
        """Читает кадры до паузы wait (сек) или пока не придёт ответ по wid until. -> был ли большой кадр каталога."""
        nonlocal frames
        big, t_end = False, time.time() + wait
        ws.settimeout(0.5)
        while time.time() < min(t_end, deadline):
            try:
                op, data = ws.recv_data()
            except websocket.WebSocketTimeoutException:
                continue
            if op == websocket.ABNF.OPCODE_CLOSE:
                raise ConnectionError("Винлайн закрыл соединение")
            if op != websocket.ABNF.OPCODE_BINARY:
                continue
            raw = _gunzip(data)
            if not raw:
                continue
            if len(raw) > 200_000:
                big = True
                t_end = time.time() + 0.8                      # каталог пришёл — дальше ждём недолго
                continue
            r = parse_detail(raw)
            if r and r[1]:
                frames += 1
                if r[0] in want:
                    got[r[0]] = r[1]
                    if r[0] == until:
                        return big
                else:
                    other.add(r[0])
        return big

    want = set(wids)
    try:
        for frame in ("lang", "AA==", "data", "WINLINE", "getdate"):
            ws.send(frame)
        if not pump(25):                                       # ждём большой кадр каталога
            log("Винлайн: каталог не пришёл")
        for wid in wids:
            if time.time() > deadline:
                break
            ws.send("event.plus")
            ws.send(base64.b64encode(struct.pack("<I", wid) + b"\x00").decode())
            pump(2.5, until=wid)
            if len(got) == 0 and wids.index(wid) >= 2:          # первые три запроса без ответа — дальше нет смысла
                break
    finally:
        try:
            ws.close()
        except Exception:
            pass
    if want - set(got):
        log("Винлайн: страниц получено %d из %d (кадров с рынками %d, чужих id %d)" % (len(got), len(want), frames, len(other)))
    return got


def tg_send_file(cfg, path, caption=""):
    import uuid
    b = uuid.uuid4().hex
    with open(path, "rb") as fh:
        data = fh.read()
    parts = []
    for k, v in (("chat_id", str(cfg["chat_id"])), ("caption", caption)):
        parts.append(("--%s\r\nContent-Disposition: form-data; name=\"%s\"\r\n\r\n%s\r\n" % (b, k, v)).encode())
    parts.append(("--%s\r\nContent-Disposition: form-data; name=\"document\"; filename=\"%s\"\r\n"
                  "Content-Type: application/json\r\n\r\n" % (b, os.path.basename(path))).encode())
    parts += [data, ("\r\n--%s--\r\n" % b).encode()]
    req = urllib.request.Request("https://api.telegram.org/bot%s/sendDocument" % cfg["bot_token"],
                                 data=b"".join(parts), headers={"Content-Type": "multipart/form-data; boundary=" + b})
    try:
        urllib.request.urlopen(req, timeout=60).read()
        return True
    except Exception as e:
        log("sendDocument:", type(e).__name__)
        return False


def run_probe(cfg, n):
    """Сбор данных для калибровки новых рынков: страницы матчей Винлайна + все факторы Фонбета -> probe.json в Telegram."""
    doc = fonbet_fetch(cfg)
    msgs = winline_fetch(cfg)
    fon = fonbet_parse(doc)
    pairs = match_events(winline_events(msgs), fon)
    cfmap = {c.get("e"): c for c in doc.get("customFactors", [])}
    kids = collections.defaultdict(list)
    for e in doc.get("events", []):
        if e.get("parentId"):
            kids[e["parentId"]].append(e)

    def raw(eid):
        return [{"f": x["f"], "v": x.get("v"), "p": x.get("p")} for x in (cfmap.get(eid) or {}).get("factors", [])]

    cand = []
    for w, f, sw in pairs:
        ks = {k["kind"]: raw(k["id"]) for k in kids.get(f["id"], []) if k["id"] in cfmap}
        if ks.get(400100) and w.get("wid"):
            cand.append((w, f, sw, ks))
    cand.sort(key=lambda r: r[0]["start"])
    cand = cand[:n]
    log("пробa: матчей с угловыми у обеих БК:", len(cand))
    det = winline_details(cfg, [c[0]["wid"] for c in cand]) if cand else {}
    out = []
    for w, f, sw, ks in cand:
        d = det.get(w["wid"])
        log("  %s – %s: %s" % (w["home"], w["away"], ("%d записей" % len(d)) if d else "нет ответа"))
        out.append({"home": w["home"], "away": w["away"], "swapped": sw, "start": w["start"], "league": f["league"],
                    "wid": w["wid"], "winline": d or [], "fonbet_main": raw(f["id"]), "fonbet_kids": ks,
                    "winline_catalog": w["markets"], "fonbet_catalog": f["markets"]})
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "probe.json")
    with open(path, "w", encoding="utf-8") as fh:
        json.dump(out, fh, ensure_ascii=False)
    log("записано %s (%d матчей)" % (path, len(out)))
    if cfg["bot_token"] and cfg["chat_id"] and out:
        log("отправлен в Telegram" if tg_send_file(cfg, path, "probe.json: данные для калибровки угловых") else "не отправлен")


# ============================================================ Фонбет

TOTAL_PAIRS = [(1696, 1697), (1727, 1728), (1730, 1731), (1733, 1734), (930, 931), (1736, 1737), (1739, 1791),
               (1793, 1794), (1796, 1797), (1799, 1800), (1802, 1803), (1848, 1849)]   # добавлены и сверены с Винлайном
HCP_PAIRS = [(910, 912), (927, 928), (989, 991), (1569, 1572), (1672, 1675),
             (1677, 1678), (1680, 1681), (1683, 1684), (1686, 1687), (1689, 1690), (1692, 1718), (1845, 1846)]
SPORTS_OK = {"football", "hockey", "tennis", "basketball", "table-tennis", "volleyball", "handball", "futsal",
             "baseball", "rugby", "am-football", "floorball", "bandy", "waterpolo", "billiard", "esports"}
IT1_PAIRS = [(1809, 1810), (1812, 1813), (1815, 1816), (1818, 1819), (1821, 1822), (1824, 1825), (1827, 1828)]   # инд. тотал хозяев (больше, меньше)
IT2_PAIRS = [(1854, 1871), (1873, 1874), (1880, 1881)]                                                          # инд. тотал гостей
FAKE_LEAGUE = re.compile(r"кибер|esoccer|e-?football|fifa|virtual|виртуал", re.I)


def _sport_of(sports, sid):
    s, seen = sports.get(sid), 0
    while s and s.get("kind") != "sport" and seen < 8:
        s = sports.get(s.get("parentId"))
        seen += 1
    return s


def _fon_markets(f, pre, extra=False):
    """Рынки из словаря факторов f (id -> {v, p}); pre — префикс периода ("" матч, "1H:" первый тайм).
    extra=True (футбол): ещё двойной шанс, обе забьют и индивидуальные тоталы."""
    mk = {}
    if extra:
        if 924 in f and 925 in f and 1571 in f:
            mk[pre + "DC"] = {"1X": float(f[924]["v"]), "X2": float(f[925]["v"]), "12": float(f[1571]["v"])}
        if 4241 in f and 4242 in f:
            mk[pre + "BTTS"] = {"Y": float(f[4241]["v"]), "N": float(f[4242]["v"])}
        for fam, prs in (("IT1", IT1_PAIRS), ("IT2", IT2_PAIRS)):
            for over, under in prs:
                if over in f and under in f and "p" in f[over] and f[over]["p"] == f[under].get("p") and f[over]["p"] % 50 == 0:
                    mk["%s%s:%.2f" % (pre, fam, f[over]["p"] / 100)] = {"O": float(f[over]["v"]), "U": float(f[under]["v"])}
    if 921 in f and 922 in f and 923 in f:
        mk[pre + "1X2"] = {"1": float(f[921]["v"]), "X": float(f[922]["v"]), "2": float(f[923]["v"])}
    for over, under in TOTAL_PAIRS:
        if over in f and under in f and "p" in f[over] and f[over]["p"] == f[under].get("p"):
            p = f[over]["p"]
            if p % 50 == 0:
                mk[pre + "TOTAL:%.2f" % (p / 100)] = {"O": float(f[over]["v"]), "U": float(f[under]["v"])}
    for home, away in HCP_PAIRS:
        if home in f and away in f and "p" in f[home] and "p" in f[away]:
            ph, pa = f[home]["p"], f[away]["p"]
            if ph == -pa and ph % 50 == 0:
                mk[pre + "HCP:%.2f" % (ph / 100 + 0.0)] = {"1": float(f[home]["v"]), "2": float(f[away]["v"])}
    return mk


ESPORTS_SKIP = re.compile(r"H2H|\b2\s?[xх]\s?2\b|Итоги", re.I)       # раундовые мини-матчи и «победитель турнира»


def fon_esports_markets(f):
    """Киберспорт Фонбета: победитель матча (921/923) и фора/тотал ПО КАРТАМ (3262/3263, 3265/3266, 3274/3275).
    Факторы 910/927/930 и т.п. в киберспорте — раунды и киллы, их не берём."""
    mk = {}
    if 921 in f and 923 in f:
        mk["ML"] = {"1": float(f[921]["v"]), "2": float(f[923]["v"])}
    for hf, af in ((3262, 3263), (3265, 3266)):
        if hf in f and af in f and "p" in f[hf] and f[af].get("p") == -f[hf]["p"] and f[hf]["p"] % 50 == 0 and abs(f[hf]["p"]) <= 350:
            mk["HCP:%.2f" % (f[hf]["p"] / 100 + 0.0)] = {"1": float(f[hf]["v"]), "2": float(f[af]["v"])}
    if 3274 in f and 3275 in f and "p" in f[3274] and f[3274]["p"] == f[3275].get("p") and f[3274]["p"] % 50 == 0 and f[3274]["p"] <= 450:
        mk["TOTAL:%.2f" % (f[3274]["p"] / 100)] = {"O": float(f[3274]["v"]), "U": float(f[3275]["v"])}
    return mk


def fonbet_parse(doc):
    """Только футбол, только прематч. Рынки: 1X2, TOTAL:L {O,U}, HCP:L {1,2} (L — линия хозяев),
    те же рынки на 1-й тайм (префикс 1H:), BTTS {Y,N}, DC {1X,X2,12}."""
    sports = {s["id"]: s for s in doc.get("sports", [])}
    events = {e["id"]: e for e in doc.get("events", [])
              if e.get("level") == 1 and e.get("kind") == 1 and e.get("team1") and e.get("team2")}
    first_half = {e["parentId"]: e["id"] for e in doc.get("events", [])
                  if e.get("level") == 2 and e.get("kind") == 100201 and e.get("place") == "line"}
    second_half = {e["parentId"]: e["id"] for e in doc.get("events", [])
                   if e.get("level") == 2 and e.get("kind") == 100202 and e.get("place") == "line"}
    corner = {e["parentId"]: e["id"] for e in doc.get("events", [])
              if e.get("kind") == 400100 and e.get("place") == "line"}
    corner_h1 = {e["parentId"]: e["id"] for e in doc.get("events", [])
                 if e.get("kind") == 10100201 and e.get("place") == "line"}
    cfmap = {c.get("e"): c for c in doc.get("customFactors", [])}

    def fac(eid):
        return {x["f"]: x for x in (cfmap.get(eid) or {}).get("factors", []) if x.get("v", 0) > 1.0}

    out = []
    for eid, ev in events.items():
        if eid not in cfmap or ev.get("place") != "line":
            continue
        top = _sport_of(sports, ev.get("sportId")) or {}
        sk = top.get("alias") or ""
        if sk not in SPORTS_OK:
            continue
        league = sports.get(ev.get("sportId"), {}).get("name", "")
        if sk == "esports":
            if ESPORTS_SKIP.search(league):
                continue
            mk = fon_esports_markets(fac(eid))
            if mk:
                out.append({"bk": "fonbet", "league": league, "home": ev["team1"], "away": ev["team2"],
                            "start": int(ev["startTime"]), "markets": mk, "id": ev["id"],
                            "sport": top.get("name", ""), "sk": sk})
            continue
        if FAKE_LEAGUE.search(league):
            continue
        f = fac(eid)
        mk = _fon_markets(f, "")
        if sk != "football":                                    # другие виды спорта: победа 2 исхода + тоталы/форы
            if "1X2" not in mk and 921 in f and 923 in f and 922 not in f:
                mk["ML"] = {"1": float(f[921]["v"]), "2": float(f[923]["v"])}
            if mk:
                out.append({"bk": "fonbet", "league": league, "home": ev["team1"], "away": ev["team2"],
                            "start": int(ev["startTime"]), "markets": mk, "id": ev["id"],
                            "sport": top.get("name", ""), "sk": sk})
            continue
        mk = _fon_markets(f, "", extra=True)
        if eid in first_half:
            mk.update(_fon_markets(fac(first_half[eid]), "1H:", extra=True))
        if eid in second_half:
            mk.update(_fon_markets(fac(second_half[eid]), "2H:", extra=True))
        if eid in corner and corner[eid] in cfmap:               # угловые: только тоталы и форы (факторы те же)
            cm = _fon_markets(fac(corner[eid]), "CRN:")
            mk.update({k: v for k, v in cm.items() if k != "CRN:1X2"})
            if corner[eid] in corner_h1:
                cm = _fon_markets(fac(corner_h1[corner[eid]]), "1H:CRN:")
                mk.update({k: v for k, v in cm.items() if k != "1H:CRN:1X2"})
        if mk:
            out.append({"bk": "fonbet", "league": league, "home": ev["team1"], "away": ev["team2"],
                        "start": int(ev["startTime"]), "markets": mk, "id": ev["id"],
                        "sport": "Футбол", "sk": "football"})
    return out


# ============================================================ Винлайн (бинарный протокол)
# Формат разобран по реальному дампу и сверен с экраном Винлайна:
#   заголовок матча:  <u32 время (МСК-как-UTC)> <u16> <u16 len><home> <u16 len><away>
#   запись коэф.:     0x04 <u32 id> <u16 код> 10 27 10 27 <тело>
#   код 490  = 1X2:     <1><X><2>, каждое u16 /100
#   код 1073 = фора:    <u8 знак: 0 ноль / 1 минус у хозяев / 2 плюс у хозяев> <u16 линия/100> <хозяева><гости>
#   код 1049 = тотал:   <u16 линия/100> <больше><меньше>
#   код 985 = тотал 1-го тайма (как 1049), 988 = фора 1-го тайма (как 1073), 2 = 1X2 1-го тайма (как 490),
#   код 58 = обе забьют: <да><нет>
#   записи своего матча идут от заголовка до скачка id > WINDOW; дальше блоки других матчей.

REC = re.compile(rb"\x04(?P<id>....)(?P<code>..)\x10\x27\x10\x27", re.S)
LETTERS = re.compile(r"[A-Za-zА-Яа-яЁё]{2}")
WINDOW = 3_000
TZ_SHIFT = 3 * 3600


def _u16(b, o):
    return struct.unpack_from("<H", b, o)[0]


def _rs(b, i):
    if i + 2 > len(b):
        return None
    n = _u16(b, i)
    if n < 1 or n > 60 or i + 2 + n > len(b):
        return None
    try:
        s = b[i + 2:i + 2 + n].decode("utf-8")
    except UnicodeDecodeError:
        return None
    s = s.rstrip("".join(chr(c) for c in range(32)))       # у части названий в конце служебный байт (напр. 0x1B)
    return (s, n) if s and s.isprintable() else None


def winline_headers(m, now):
    lo = int(now) + TZ_SHIFT - 86400
    hi = int(now) + TZ_SHIFT + 45 * 86400
    tops = set(range(lo >> 24, (hi >> 24) + 1))
    heads, i, n = [], 0, len(m) - 12
    while i < n:
        if m[i + 3] in tops:
            t = struct.unpack_from("<I", m, i)[0]
            if lo <= t <= hi:
                h = _rs(m, i + 6)
                if h:
                    k = i + 6 + 2 + h[1]
                    a = _rs(m, k)
                    if a and LETTERS.search(h[0]) and LETTERS.search(a[0]):
                        end = k + 2 + a[1]
                        wid = struct.unpack_from("<I", m, i - 27)[0] if i >= 27 else 0
                        heads.append((i, t, h[0], a[0], end, wid))
                        i = end
                        continue
        i += 1
    return heads


def _parse_event(region):
    st = [(x.start(), x.end(), struct.unpack("<I", x.group("id"))[0], struct.unpack("<H", x.group("code"))[0])
          for x in REC.finditer(region)]
    base = next((i for (_, _, i, c) in st if c in (490, 491)), None)
    if base is None:
        return None
    mk, started = {}, False
    mixed = len({i for (_, _, i, c) in st if c in (490, 491)}) > 1      # в области видны записи чужого матча -> верим только 1X2
    for n, (s, e, idv, code) in enumerate(st):
        if mixed and code not in (490, 491):
            continue
        if code in (490, 491) and idv != base:             # началась 1X2 другого матча -> дальше чужие записи
            break
        if abs(idv - base) > WINDOW:
            if started:
                break
            continue
        started = True
        e2 = st[n + 1][0] if n + 1 < len(st) else len(region)
        b = region[e:e2]
        u = lambda o: _u16(b, o) / 100.0
        if code == 490 and len(b) >= 6 and "1X2" not in mk:
            mk["1X2"] = {"1": u(0), "X": u(2), "2": u(4)}
        elif code == 491 and len(b) >= 4 and "ML" not in mk:     # победа, 2 исхода (хоккей-теннис-баскетбол и т.п.)
            mk["ML"] = {"1": u(0), "2": u(2)}
        elif code == 1073 and len(b) >= 7 and b[0] in (0, 1, 2):
            line = u(1)
            hl = 0.0 if b[0] == 0 else (-line if b[0] == 1 else line)
            mk.setdefault("HCP:%.2f" % (hl + 0.0), {"1": u(3), "2": u(5)})
        elif code == 1049 and len(b) >= 6:
            line = u(0)
            if (line * 2) == int(line * 2):
                mk.setdefault("TOTAL:%.2f" % line, {"O": u(2), "U": u(4)})
        elif code == 985 and len(b) >= 6:                       # тотал 1-го тайма
            line = u(0)
            if (line * 2) == int(line * 2):
                mk.setdefault("1H:TOTAL:%.2f" % line, {"O": u(2), "U": u(4)})
        elif code == 988 and len(b) >= 7 and b[0] in (0, 1, 2):  # фора 1-го тайма
            line = u(1)
            hl = 0.0 if b[0] == 0 else (-line if b[0] == 1 else line)
            mk.setdefault("1H:HCP:%.2f" % (hl + 0.0), {"1": u(3), "2": u(5)})
        elif code == 2 and len(b) >= 6:                         # 1X2 1-го тайма
            mk.setdefault("1H:1X2", {"1": u(0), "X": u(2), "2": u(4)})
        elif code == 58 and len(b) >= 4:                        # обе забьют
            mk.setdefault("BTTS", {"Y": u(0), "N": u(2)})
    for k in list(mk):                              # закрытые котировки (0) -> рынок выкидываем
        if any(v <= 1.0 for v in mk[k].values()):
            del mk[k]
    return mk or None


def winline_events(msgs, now=None):
    now = now or time.time()
    out = []
    for m in msgs:
        if len(m) < 20_000:
            continue
        heads = winline_headers(m, now)
        for k, (i, t, h, a, end, wid) in enumerate(heads):
            nxt = heads[k + 1][0] if k + 1 < len(heads) else len(m)
            mk = _parse_event(m[end:nxt])
            if mk:
                out.append({"bk": "winline", "home": h, "away": a, "start": t - TZ_SHIFT, "markets": mk, "wid": wid})
    return out


# ============================================================ Бетсити (обычный JSON по HTTPS, ad.betcity.ru)
#   GET  /d/off/champs?ids_sp=<спорт>      — чемпионаты вида спорта (id_ch, is_future, cols = число матчей на 24/48/72 ч)
#   POST /d/off/events?add=dep_events      — тело ids=<чемп1,чемп2>: матчи с основными рынками + дочерние события (угловые и т.п.)
#   GET  /d/off/ext?ids=<матч>             — все рынки матча (группы 71 = фора, 112 = тотал, 25 = исходы по таймам)
#   рынок в блоках: Kf_F1/Kf_F2 + F1 (линия хозяев) = фора; Tot + Tm (меньше) + Tb (больше) = тотал; P1/X/P2 = исход; 1X/12/X2 = ДШ
#   угловые — дочернее событие «УГЛ Хозяева – УГЛ Гости» (в depends родителя type = 1), у него те же группы.
BC_SPORTS = {1: "football", 7: "hockey", 2: "tennis", 3: "basketball", 12: "volleyball", 46: "table-tennis",
             8: "handball", 19: "futsal", 5: "baseball", 13: "rugby", 6: "am-football", 57: "floorball",
             17: "bandy", 24: "waterpolo", 23: "billiard", 73: "esports"}
BC_HOST = "https://ad.betcity.ru"


class _V4Conn(http.client.HTTPSConnection):
    """HTTPS строго по IPv4 (на части мобильных сетей IPv6-путь до Бетсити зависает на рукопожатии)."""

    def connect(self):
        last = OSError("нет адресов IPv4")
        for fam, typ, proto, _, addr in socket.getaddrinfo(self.host, self.port, socket.AF_INET, socket.SOCK_STREAM):
            try:
                sock = socket.create_connection(addr, self.timeout)
                self.sock = self._context.wrap_socket(sock, server_hostname=self.host)
                return
            except OSError as e:
                last = e
        raise last


class _V4Handler(urllib.request.HTTPSHandler):
    def https_open(self, req):
        return self.do_open(_V4Conn, req, context=ssl.create_default_context())


_BC_OPENER = urllib.request.build_opener(_V4Handler())


def _bc_req(cfg, path, data=None, timeout=40):
    sep = "&" if "?" in path else "?"
    url = "%s%s%sver=%s&csn=%s" % (BC_HOST, path, sep, cfg["betcity_ver"], cfg["betcity_csn"])
    headers = {"User-Agent": BB_UA, "Accept": "application/json, text/plain, */*", "Accept-Encoding": "gzip",
               "Accept-Language": "ru,en;q=0.9", "Origin": "https://betcity.ru", "Referer": "https://betcity.ru/",
               "Content-Type": "application/x-www-form-urlencoded"}
    if cfg.get("betcity_curl", True) and shutil.which("curl"):
        # системный curl: у части сетей рукопожатие TLS у Python зависает, а у curl проходит
        # Первое сообщение TLS у curl/Python с постквантовым обменом ~1.5 КБ — часть сетей его теряет (зависание рукопожатия).
        # Поэтому сначала просим короткий обмен X25519; если не вышло — обычный.
        last, h1, tries, i = None, bool(BC_RATE.get("h1")), (["--curves", "X25519"], []), 0
        while i < len(tries):
            cmd = ["curl", "-4", "-sS", "--compressed", "-m", str(int(timeout)), "--connect-timeout", "10"] + tries[i]
            if h1:
                cmd.append("--http1.1")
            if os.environ.get("ARB_CURL_INSECURE"):
                cmd.append("-k")
            for k, v in headers.items():
                if k != "Accept-Encoding":
                    cmd += ["-H", "%s: %s" % (k, v)]
            if data is not None:
                cmd += ["--data-raw", data]
            cmd.append(url)
            res = subprocess.run(cmd, capture_output=True, timeout=timeout + 10)
            if res.returncode == 0:
                if h1:
                    BC_RATE["h1"] = True                        # HTTP/2 у этого сайта на вашей сети сбрасывается — дальше сразу HTTP/1.1
                return json.loads(res.stdout.decode("utf-8", "replace")).get("reply") or {}
            last = OSError("curl %d: %s" % (res.returncode, res.stderr.decode("utf-8", "replace").strip()[:200]))
            if res.returncode in (92, 16, 55, 56) and not h1:
                h1 = True                                       # сервер сбросил поток HTTP/2 — пробуем HTTP/1.1
                continue
            if res.returncode not in (28, 35, 7):
                break
            i += 1
        raise last
    req = urllib.request.Request(url, data=data.encode() if data is not None else None, headers=headers)
    with _BC_OPENER.open(req, timeout=timeout) as r:
        raw = r.read()
        if (r.headers.get("Content-Encoding") or "").lower() == "gzip":
            raw = gzip.decompress(raw)
    return json.loads(raw.decode("utf-8", "replace")).get("reply") or {}


def _bc_blocks(blocks, pre, mk, want=("hcp", "tot", "win", "dc")):
    """Блоки рынков одной ставки -> рынки в нашем виде (дробные четвертные линии пропускаем)."""
    for b in (blocks or {}).values():
        if not isinstance(b, dict):
            continue
        kf = lambda x: float((b.get(x) or {}).get("kf") or 0)
        if "hcp" in want and "Kf_F1" in b and "Kf_F2" in b and "F1" in b and "F2" in b:
            h, k1, k2 = float(b["F1"]), kf("Kf_F1"), kf("Kf_F2")
            if abs(h + float(b["F2"])) < 1e-9 and (h * 2) == int(h * 2) and k1 > 1 and k2 > 1:
                mk.setdefault(pre + "HCP:%.2f" % (h + 0.0), {"1": k1, "2": k2})
        elif "tot" in want and "Tot" in b and "Tm" in b and "Tb" in b:
            t, over, under = float(b["Tot"]), kf("Tb"), kf("Tm")
            if (t * 2) == int(t * 2) and over > 1 and under > 1:
                mk.setdefault(pre + "TOTAL:%.2f" % t, {"O": over, "U": under})
        elif "win" in want and "P1" in b and "P2" in b and "Tot" not in b:
            p1, p2, x = kf("P1"), kf("P2"), kf("X")
            if p1 > 1 and p2 > 1:
                if "X" in b:
                    if x > 1:
                        mk.setdefault(pre + "1X2", {"1": p1, "X": x, "2": p2})
                else:
                    mk.setdefault(pre + "ML", {"1": p1, "2": p2})
        elif "dc" in want and "1X" in b and "12" in b and "X2" in b:
            a, c, d = kf("1X"), kf("12"), kf("X2")
            if a > 1 and c > 1 and d > 1:
                mk.setdefault(pre + "DC", {"1X": a, "X2": d, "12": c})


def _bc_it(blocks, pre, mk):
    """Индивидуальный тотал: блок IT_T1 (хозяева) / IT_T2 (гости) с Tot, Tb (больше), Tm (меньше)."""
    for name, b in (blocks or {}).items():
        if name not in ("IT_T1", "IT_T2") or not isinstance(b, dict) or "Tot" not in b:
            continue
        t = float(b["Tot"])
        over, under = float((b.get("Tb") or {}).get("kf") or 0), float((b.get("Tm") or {}).get("kf") or 0)
        if (t * 2) == int(t * 2) and over > 1 and under > 1:
            mk.setdefault("%s%s:%.2f" % (pre, "IT1" if name == "IT_T1" else "IT2", t), {"O": over, "U": under})


def _bc_yn(blocks, key, mk):
    b = (blocks or {}).get("YN")
    if isinstance(b, dict):
        y, n = float((b.get("Y") or {}).get("kf") or 0), float((b.get("N") or {}).get("kf") or 0)
        if y > 1 and n > 1:
            mk.setdefault(key, {"Y": y, "N": n})


def bc_group_markets(groups, pre, extended, football=True):
    """groups: main (все группы) или ext. extended=True: берём группы 71 (фора), 112 (тотал), 25 (по таймам),
    3/615/804 (индивидуальные тоталы), 14/137/138 (обе забьют)."""
    mk = {}
    for gid, g in (groups or {}).items():
        if not isinstance(g, dict):
            continue
        if extended:
            if str(gid) in ("71", "112"):
                for bet in (g.get("data") or {}).values():
                    _bc_blocks(bet.get("blocks"), pre, mk, want=("hcp", "tot"))
            elif str(gid) == "25" and football:
                for row in (g.get("rows") or {}).values():
                    per = {1: "1H:", 2: "2H:"}.get(row.get("num_per"))
                    if per:
                        for bet in (row.get("data") or {}).values():
                            _bc_blocks(bet.get("blocks"), per + pre, mk, want=("hcp", "tot") if pre else ("hcp", "tot", "win", "dc"))
            elif football and not pre and str(gid) in ("3", "615", "804"):     # индивидуальные тоталы: матч / 1-й / 2-й тайм
                for bet in (g.get("data") or {}).values():
                    _bc_it(bet.get("blocks"), {"3": "", "615": "1H:", "804": "2H:"}[str(gid)], mk)
            elif football and not pre and str(gid) in ("14", "137", "138"):     # обе забьют: матч / 1-й / 2-й тайм
                for bet in (g.get("data") or {}).values():
                    _bc_yn(bet.get("blocks"), {"14": "BTTS", "137": "1H:BTTS", "138": "2H:BTTS"}[str(gid)], mk)
        else:
            for bet in (g.get("data") or {}).values():
                _bc_blocks(bet.get("blocks"), pre, mk)
    return mk


def bc_esports_markets(mk, champ):
    """Киберспорт: победитель матча всегда; фора и тотал — только по КАРТАМ (в матче из 1 карты линии идут по раундам/киллам — выкидываем)."""
    m = re.search(r"из\s+(\d+)-", champ)
    n = int(m.group(1)) if m else 0
    out = {k: v for k, v in mk.items() if k == "ML"}
    if n >= 3:
        for k, v in mk.items():
            mm = re.match(r"(HCP|TOTAL):(-?[\d.]+)$", k)
            if not mm:
                continue
            line = float(mm.group(2))
            if mm.group(1) == "HCP" and abs(line) <= n // 2 + 0.5 and abs(line) % 1 == 0.5:
                out[k] = v
            elif mm.group(1) == "TOTAL" and n // 2 + 0.5 <= line <= n - 0.5 and line % 1 == 0.5:
                out[k] = v
    return out


def bc_parse(reply, now=None):
    """Ответ events (с дочерними событиями) -> матчи [{bk, home, away, start, league, markets, bid, kid, sk}]."""
    now = now or time.time()
    out, kids, parents = [], {}, {}
    for sid, s in (reply.get("sports") or {}).items():
        try:
            sk = BC_SPORTS.get(int(sid))
        except ValueError:
            continue
        if not sk:
            continue
        for cid, c in (s.get("chmps") or {}).items():
            nm = c.get("name_ch", "")
            if sk == "esports":                                         # настоящий киберспорт: без раундовых мини-матчей и «Победитель» турнира
                if c.get("is_virtual") or re.search(r"раунд|2x2|H2H|Победитель", nm):
                    continue
            elif c.get("is_cyber") or c.get("is_virtual") or FAKE_LEAGUE.search(nm):
                continue
            for eid, e in (c.get("evts") or {}).items():
                if e.get("del_ev") or not e.get("name_ht") or not e.get("name_at"):
                    continue
                if e.get("dep_id_ev"):                                  # дочернее: угловые
                    if str(e.get("name_ht", "")).startswith("УГЛ "):
                        kids[int(eid)] = e
                    continue
                if e.get("is_online") or e.get("time_name") or int(e.get("date_ev") or 0) < now:
                    continue                                            # только прематч
                parents[int(eid)] = (sk, c, e)
    for eid, (sk, c, e) in parents.items():
        mk = bc_group_markets(e.get("main"), "", False)
        if sk != "football":
            mk = {k: v for k, v in mk.items() if k != "DC"}
        if sk == "esports":
            mk = bc_esports_markets(mk, c.get("name_ch", ""))
        kid = next((int(d["id_ev"]) for d in (e.get("depends") or []) if d.get("type") == 1 and int(d["id_ev"]) in kids), None)
        if kid and sk == "football":
            cm = bc_group_markets(kids[kid].get("main"), "CRN:", False)
            mk.update({k: v for k, v in cm.items() if k.startswith(("CRN:HCP", "CRN:TOTAL"))})
        if mk:
            out.append({"bk": "betcity", "home": e["name_ht"], "away": e["name_at"], "start": int(e["date_ev"]),
                        "league": c.get("name_ch", ""), "markets": mk, "bid": eid, "kid": kid, "sk": sk})
    return out


def bc_ext_markets(reply, eid, pre, football=True):
    """Ответ ext по матчу eid -> рынки (много линий)."""
    for s in (reply.get("sports") or {}).values():
        for c in (s.get("chmps") or {}).values():
            e = (c.get("evts") or {}).get(str(eid))
            if e:
                return bc_group_markets(e.get("ext"), pre, True, football=football)
    return {}


BC_LOCK = threading.Lock()
BC_RATE = {"next": 0.0, "gap": None, "tok": None, "tok_t": 0.0}


def _bc_throttle(cfg):
    """Ритм запросов к Бетсити. 1) пауза между запросами (при ошибках растёт, при успехах возвращается);
    2) «ведро»: Бетсити пускает серию запросов подряд, а потом только понемногу — в ведре betcity_burst запросов, пополняется betcity_per_min в минуту;
    когда ведро пусто, ждём. После блокировки ведро пустое: сразу после неё много запросов подряд нельзя."""
    base = float(cfg["betcity_gap"])
    with BC_LOCK:
        gap = BC_RATE["gap"] or base
        now = time.time()
        wait = max(0.0, BC_RATE["next"] - now)
        BC_RATE["next"] = max(now, BC_RATE["next"]) + gap * random.uniform(0.8, 1.3)
        cap, rate = float(cfg["betcity_burst"]), float(cfg["betcity_per_min"]) / 60.0
        if BC_RATE["tok"] is None:
            BC_RATE["tok"], BC_RATE["tok_t"] = float(cfg["betcity_burst_start"]), now
        tok = min(cap, BC_RATE["tok"] + (now - BC_RATE["tok_t"]) * rate)
        if tok < 1:
            wait = max(wait, (1 - tok) / rate)
            tok = 1.0
        BC_RATE["tok"], BC_RATE["tok_t"] = tok - 1.0, now + wait          # токен списан в момент отправки запроса
    if wait:
        time.sleep(wait)


def _bc_is_conn(e):
    """Соединение не устанавливается / обрыв по времени — признак блокировки адреса (а не ошибки одного запроса)."""
    t = str(e)
    return "curl 28" in t or "curl 7:" in t or "timed out" in t


def _bc_ok(cfg):
    with BC_LOCK:
        BC_CACHE["fails"] = 0
        BC_CACHE["dfails"] = 0
        g = BC_RATE["gap"]
        if g and g > float(cfg["betcity_gap"]):
            BC_RATE["gap"] = max(float(cfg["betcity_gap"]), g * 0.9)


def _bc_fail(cfg, what, connect=False, detail=False):
    """Ошибка или блокировка: растим паузу между запросами и откладываем следующую загрузку (1, 2, 4… минуты).
    Ошибка страницы матча (detail) без обрыва соединения откладывает только страницы матчей, основные данные грузятся дальше."""
    if detail and not connect:
        with BC_LOCK:
            BC_CACHE["dfails"] = BC_CACHE.get("dfails", 0) + 1
            BC_CACHE["dpause"] = time.time() + min(600, 60 * 2 ** (BC_CACHE["dfails"] - 1))
            wait = BC_CACHE["dpause"] - time.time()
        log("Бетсити: %s — страницы матчей на паузе %d с, основные данные грузятся дальше" % (what, wait))
        return
    with BC_LOCK:
        BC_CACHE["fails"] = BC_CACHE.get("fails", 0) + 1
        n = BC_CACHE["fails"]
        BC_RATE["gap"] = min(12.0, (BC_RATE["gap"] or float(cfg["betcity_gap"])) * 1.5)
        if connect:
            BC_RATE["tok"], BC_RATE["tok_t"] = 0.0, time.time() + 720      # после блокировки ведро пустое
        # обрыв соединения = блок адреса, он длится ~10 минут после последних запросов (измерено): ждём 12 минут, дальше 24 и т. д. (максимум 40)
        BC_CACHE["pause"] = time.time() + (min(2400, 720 * 2 ** (n - 1)) if connect else min(600, 60 * 2 ** (n - 1)))
        gap = BC_RATE["gap"]
    log("Бетсити: %s — пауза %d с, интервал между запросами %.1f с" % (what, BC_CACHE["pause"] - time.time(), gap))
    if connect and n >= 2:
        notify_block(cfg, "betcity", "Бетсити")


def betcity_fetch(cfg):
    """Бетсити без блокировок: каждый цикл догружаем только устаревшие пачки чемпионатов (самые старые первыми),
    запросы идут с паузами, свежие ответы копятся в BC_CACHE["batches"]. -> список ответов events за последние betcity_max_age секунд.
    Матчи уже известных чемпионатов грузятся раньше, чем списки чемпионатов: один спорт с ошибкой больше не блокирует остальные."""
    now = time.time()
    hours = str(cfg["betcity_hours"])
    sports = [sid for sid, sk in BC_SPORTS.items() if sk in cfg["betcity_sports"]]
    chs = BC_CACHE.setdefault("chs", {})
    batches = BC_CACHE.setdefault("batches", {})
    bad = BC_CACHE.setdefault("chs_bad", {})                    # спорт -> когда пробовать список чемпионатов снова
    t_end = now + cfg["betcity_budget"]
    n = max(1, int(cfg["betcity_batch"]))
    done = [0]

    def can_go():
        return time.time() >= BC_CACHE.get("pause", 0) and time.time() <= t_end

    def is_conn(e):
        return "curl 28" in str(e) or "curl 7" in str(e) or "timed out" in str(e)

    def load_champs():
        for sid in sports:
            c = chs.get(sid)
            if (c and time.time() - c[0] < cfg["betcity_champs_ttl"]) or time.time() < bad.get(sid, 0):
                continue                                        # список свежий или у этого спорта перерыв после ошибки
            if not can_go():
                return
            try:
                _bc_throttle(cfg)
                ch = (_bc_req(cfg, "/d/off/champs?rev=4&strip=dep_champs&ids_sp=%d" % sid, timeout=20).get("sports") or {}).get(str(sid)) or {}
                ids = [str(c["id_ch"]) for c in (ch.get("chmps") or {}).values()
                       if not c.get("is_future") and not c.get("is_stat") and (c.get("cols") or {}).get(hours, 0) > 0]
                chs[sid] = (time.time(), ids)
                _bc_ok(cfg)
                log("Бетсити: спорт %d — чемпионатов всего %d, с матчами на %s ч: %d" % (sid, len(ch.get("chmps") or {}), hours, len(ids)))
            except Exception as e:
                bad[sid] = time.time() + 300                    # этот спорт не раньше чем через 5 минут, остальные грузим дальше
                _bc_fail(cfg, "чемпионаты спорта %d: %s: %s" % (sid, type(e).__name__, e), _bc_is_conn(e))
                return

    def jobs():
        out = []
        for sid in sports:
            ids = (chs.get(sid) or (0, []))[1]
            out += [tuple(ids[i:i + n]) for i in range(0, len(ids), n)]
        return out

    def load_batches():
        due = sorted((j for j in jobs() if time.time() - (batches.get(j) or (0, None))[0] >= cfg["betcity_refresh"]),
                     key=lambda j: (batches.get(j) or (0, None))[0])
        while due and can_go():
            j = due.pop(0)
            try:
                _bc_throttle(cfg)
                r = _bc_req(cfg, "/d/off/events?rev=6&add=dep_events", "ids=" + ",".join(j), timeout=60)
                if not sum(len(s.get("chmps") or {}) for s in (r.get("sports") or {}).values()):
                    raise ValueError("пустой ответ (возможно, блокировка IP)")
                batches[j] = (time.time(), r)
                _bc_ok(cfg)
                done[0] += 1
            except Exception as e:
                _bc_fail(cfg, "пачка из %d чемпионатов: %s: %s" % (len(j), type(e).__name__, e), _bc_is_conn(e))
                break
        return due

    if not any(chs.get(sid) for sid in sports):
        load_champs()                                           # совсем ничего не знаем — без списка чемпионатов начать нельзя
    due = load_batches()                                        # матчи известных чемпионатов — в первую очередь
    load_champs()                                               # затем списки чемпионатов, которые устарели или не загрузились
    due = load_batches()
    cur = set(jobs())
    for j in [j for j, (t, _) in batches.items() if j not in cur or time.time() - t > cfg["betcity_max_age"]]:
        del batches[j]                                          # устаревшие пачки не используем: старые коэффициенты дают ложные вилки
    BC_CACHE["done"] = (len(batches), len(cur))
    if done[0] or due:
        log("Бетсити: обновлено пачек %d, в запасе %d из %d (ждут обновления: %d)" % (done[0], len(batches), len(cur), len(due)))
    BC_CACHE["t"] = min((t for t, _ in batches.values()), default=0.0)
    return [r for _, r in batches.values()]


def betcity_events(replies, now=None):
    out, seen = [], set()
    for r in replies:
        for ev in bc_parse(r, now):
            if ev["bid"] not in seen:
                seen.add(ev["bid"])
                out.append(ev)
    return out


def add_bc_details(cfg, pairs):
    """Все линии и угловые — только для ближайших совпавших матчей, понемногу за цикл; результат хранится betcity_detail_ttl секунд."""
    det = BC_CACHE.setdefault("detail", {})
    cand = sorted(pairs, key=lambda p: p[0]["start"])[:cfg["betcity_detail_max"]]
    now, fetched, left = time.time(), 0, 0
    for w, f, sw in cand:
        c = det.get(w["bid"])
        if not c or now - c[0] > cfg["betcity_detail_ttl"]:
            if fetched >= cfg["betcity_detail_per_cycle"] or time.time() < max(BC_CACHE.get("pause", 0), BC_CACHE.get("dpause", 0)):
                left += 1
            else:
                try:
                    _bc_throttle(cfg)
                    r = _bc_req(cfg, "/d/off/ext?rev=3&ids=%d" % w["bid"], timeout=40)
                    mk = bc_ext_markets(r, w["bid"], "", football=(w["sk"] == "football"))
                    if w.get("kid") and w["sk"] == "football":
                        _bc_throttle(cfg)
                        mk.update(bc_ext_markets(_bc_req(cfg, "/d/off/ext?rev=3&ids=%d" % w["kid"], timeout=40), w["kid"], "CRN:"))
                    if w["sk"] != "football":
                        mk = {k: v for k, v in mk.items() if not k.startswith("1H:")}
                    c = det[w["bid"]] = (time.time(), mk)
                    fetched += 1
                    _bc_ok(cfg)
                except Exception as e:
                    _bc_fail(cfg, "страница матча %s: %s: %s" % (w.get("bid"), type(e).__name__, e), _bc_is_conn(e), detail=True)
                    left += 1
                    c = det.get(w["bid"])
        if c:
            w["markets"].update(c[1])
    for b in [b for b, (t, _) in det.items() if now - t > cfg["betcity_detail_ttl"] * 3]:
        del det[b]
    if fetched or left:
        log("Бетсити: страницы матчей обновлено %d, ждут очереди %d из %d" % (fetched, left, len(cand)))


# ============================================================ Леон (обычный JSON по HTTPS, leon.ru/api-2)
#   GET /api-2/betline/sports?ctag=..&flags=urlv2            — виды спорта -> регионы -> лиги (id, prematch = число матчей)
#   GET /api-2/betline/events/all?ctag=..&league_id=<лига>   — матчи лиги с основными рынками
#   GET /api-2/betline/event/all?ctag=..&eventId=<матч>&flags=..  — страница матча: все рынки (много линий, угловые, тайм)
#   рынок: name, typeTag (REGULAR / TOTAL / HANDICAP), specifiers {total|hcp: линия}, runners [{tags, price, open}]
#   фора: hcp — линия хозяев; тотал: UNDER / OVER; "Азиатские" (четвертные) линии пропускаем
LEON_HOST = "https://leon.ru"
LEON_FAM = {"Soccer": "football", "IceHockey": "hockey", "Tennis": "tennis", "Basketball": "basketball",
            "Volleyball": "volleyball", "TableTennis": "table-tennis", "Handball": "handball", "Futsal": "futsal",
            "Baseball": "baseball", "RugbyUnion": "rugby", "RugbyLeague": "rugby", "AmericanFootball": "am-football",
            "Floorball": "floorball", "ESport": "esports"}
LEON_FLAGS = "reg,urlv2,orn2,cn,mm3,ssn,rrc,nodup,cmg"
LEON_FLAGS_FULL = "reg,urlv2,orn2,cn,mm3,ssn,rrc,nodup,cmg,smgv2,outv2,wd4"
# Названия «целого матча» по видам спорта. Рынки с периодом/сетом/партией (periodnr, setnr, gamenr…) берём только футбольные «1-й/2-й тайм».
LEON_TOT = {"football": ("Тотал",), "hockey": ("Тотал",), "basketball": ("Тотал",), "handball": ("Тотал",),
            "futsal": ("Тотал",), "baseball": ("Тотал",), "rugby": ("Тотал",), "am-football": ("Тотал",),
            "floorball": ("Тотал",), "esports": ("Тотал карт", "Тотал по картам"), "tennis": ("Тотал геймов",), "table-tennis": ("Тотал очков",),
            "volleyball": ("Тотал очков",)}
LEON_HCP = {"football": ("Фора",), "hockey": ("Фора",), "basketball": ("Фора",), "handball": ("Фора",),
            "futsal": ("Фора",), "baseball": ("Фора",), "rugby": ("Фора",), "am-football": ("Фора",),
            "floorball": ("Фора",), "esports": ("Фора по картам",), "tennis": ("Фора по геймам",), "table-tennis": ("Фора",),
            "volleyball": ("Фора по очкам",)}
_LEON_PERIOD = {"1-й тайм: ": "1H:", "2-й тайм: ": "2H:"}


LEON_UA = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/152.0.0.0 Safari/537.36"
LEON_JAR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "leon_cookies.txt")
_LEON_OPENER = urllib.request.build_opener(_V4Handler(), urllib.request.HTTPCookieProcessor())


def _leon_req(cfg, path, timeout=40):
    sep = "&" if "?" in path else "?"
    url = "%s%s%sctag=%s" % (LEON_HOST, path, sep, cfg["leon_ctag"])
    # Без полного набора браузерных заголовков Леон отвечает 403; с ним — 307 и куки spid/spsc, после чего повторный запрос проходит.
    headers = {"User-Agent": LEON_UA, "Accept": "*/*", "Accept-Language": "ru,en;q=0.9", "Referer": "https://leon.ru/",
               "sec-fetch-dest": "empty", "sec-fetch-mode": "cors", "sec-fetch-site": "same-origin",
               "x-app-platform": "web", "x-app-env": "prod", "x-app-language": "ru_RU", "x-app-layout": "desktop",
               "x-app-version": cfg["leon_ver"], "x-app-os": "windows", "x-app-browser": "yandex", "x-app-modernity": "modern",
               "x-app-rendering": "csr", "x-app-skin": "default", "x-requested-uri": "/"}
    if cfg.get("leon_curl", True) and shutil.which("curl"):
        last = None
        for curves in (["--curves", "X25519"], []):
            cmd = ["curl", "-4", "-sS", "--compressed", "-m", str(int(timeout)), "--connect-timeout", "10",
                   "-L", "--max-redirs", "4", "-b", LEON_JAR, "-c", LEON_JAR,
                   "-w", "\n%{http_code}"] + curves
            if os.environ.get("ARB_CURL_INSECURE"):
                cmd.append("-k")
            for k, v in headers.items():
                cmd += ["-H", "%s: %s" % (k, v)]
            cmd.append(url)
            res = subprocess.run(cmd, capture_output=True, timeout=timeout + 10)
            if res.returncode == 0:
                body, _, code = res.stdout.decode("utf-8", "replace").rpartition("\n")
                if code != "200":
                    raise OSError("Леон ответил HTTP %s: %s" % (code, re.sub(r"\s+", " ", re.sub(r"<[^>]+>", " ", body))[:120]))
                return json.loads(body)
            last = OSError("curl %d: %s" % (res.returncode, res.stderr.decode("utf-8", "replace").strip()[:200]))
            if res.returncode not in (28, 35, 7):
                break
        raise last
    req = urllib.request.Request(url, headers=dict(headers, **{"Accept-Encoding": "gzip"}))
    with _LEON_OPENER.open(req, timeout=timeout) as r:
        raw = r.read()
        if (r.headers.get("Content-Encoding") or "").lower() == "gzip":
            raw = gzip.decompress(raw)
    return json.loads(raw.decode("utf-8", "replace"))


def _leon_line(s):
    try:
        v = float(s)
    except (TypeError, ValueError):
        return None
    return v if (v * 2) == int(v * 2) else None                 # четвертные линии (x.25 / x.75) не берём


def leon_markets(markets, sk):
    """Рынки матча Леона -> рынки в нашем виде. Закрытые рынки и закрытые исходы пропускаем."""
    mk = {}
    foot = sk == "football"
    tot_names, hcp_names = LEON_TOT.get(sk, ("Тотал",)), LEON_HCP.get(sk, ("Фора",))
    for m in markets or []:
        if not m.get("open", True):
            continue
        name, sp = m.get("name") or "", m.get("specifiers") or {}
        pre = ""
        if foot:
            for t, p in _LEON_PERIOD.items():
                if name.startswith(t):
                    pre, name = p, name[len(t):]
                    break
            if name.startswith("Тотал угловых") and "3 исхода" not in name and name == "Тотал угловых":
                pre, name = pre + "CRN:", "Тотал"
            elif name == "Фора по угловым":
                pre, name = pre + "CRN:", "Фора"
            elif name == "Победитель":
                name = "1X2" if pre else name
        run = {}
        for r in m.get("runners") or []:
            if not r.get("open", True) or not r.get("price") or float(r["price"]) <= 1:
                continue
            for t in r.get("tags") or []:
                run.setdefault(t, float(r["price"]))
        if any(k in sp for k in ("periodnr", "setnr", "gamenr", "goalnr", "cornernr", "competitor", "minute")):
            continue
        crn = pre.endswith("CRN:")
        typ = m.get("typeTag")
        if typ == "TOTAL" and (name in tot_names or (crn and name == "Тотал")):
            t = _leon_line(sp.get("total"))
            if t is not None and run.get("OVER") and run.get("UNDER") and not run.get("DRAW"):
                mk.setdefault("%sTOTAL:%.2f" % (pre, t), {"O": run["OVER"], "U": run["UNDER"]})
        elif typ == "TOTAL" and foot and name in ("Тотал хозяев", "Тотал гостей") and not crn:
            t = _leon_line(sp.get("total"))
            if t is not None and run.get("OVER") and run.get("UNDER"):
                mk.setdefault("%s%s:%.2f" % (pre, "IT1" if name == "Тотал хозяев" else "IT2", t), {"O": run["OVER"], "U": run["UNDER"]})
        elif typ == "HANDICAP" and (name in hcp_names or (crn and name == "Фора")):
            h = _leon_line(sp.get("hcp"))
            if h is not None and run.get("HOME") and run.get("AWAY") and not run.get("DRAW"):
                mk.setdefault("%sHCP:%.2f" % (pre, h + 0.0), {"1": run["HOME"], "2": run["AWAY"]})
        elif typ == "REGULAR" and not sp:
            if name.startswith("Исход 1Х2") and run.get("HOME") and run.get("DRAW") and run.get("AWAY"):
                mk.setdefault("1X2", {"1": run["HOME"], "X": run["DRAW"], "2": run["AWAY"]})
            elif name == "1X2" and run.get("HOME") and run.get("DRAW") and run.get("AWAY"):
                mk.setdefault(pre + "1X2", {"1": run["HOME"], "X": run["DRAW"], "2": run["AWAY"]})
            elif name in ("Победитель", "Победитель (включая OT и послематчевые буллиты)") or name.startswith("Победитель (включая"):
                if not foot and run.get("HOME") and run.get("AWAY") and not run.get("DRAW"):
                    mk.setdefault("ML", {"1": run["HOME"], "2": run["AWAY"]})
            elif foot and name == "Двойной исход" and run.get("HOMEDRAW") and run.get("HOMEAWAY") and run.get("DRAWAWAY"):
                mk.setdefault(pre + "DC", {"1X": run["HOMEDRAW"], "12": run["HOMEAWAY"], "X2": run["DRAWAWAY"]})
            elif foot and name == "Обе команды забьют" and run.get("YES") and run.get("NO"):
                mk.setdefault(pre + "BTTS", {"Y": run["YES"], "N": run["NO"]})
    return mk


def leon_parse(events, now=None):
    """Список матчей Леона -> [{bk, home, away, start, league, markets, bid, sk}] (только прематч)."""
    now = now or time.time()
    out = []
    for e in events or []:
        lg = e.get("league") or {}
        sk = LEON_FAM.get((lg.get("sport") or {}).get("family"))
        if not sk or e.get("betline") != "prematch" or not e.get("open", True) or e.get("status") != "OPEN":
            continue
        if FAKE_LEAGUE.search(lg.get("name", "")) or (sk != "esports" and FAKE_LEAGUE.search((lg.get("sport") or {}).get("name", ""))):
            continue
        comp = {c.get("homeAway"): c.get("name") for c in e.get("competitors") or []}
        if not comp.get("HOME") or not comp.get("AWAY"):
            continue
        start = int((e.get("kickoff") or 0) / 1000)
        if start < now:
            continue
        mk = leon_markets(e.get("markets"), sk)
        out.append({"bk": "leon", "home": comp["HOME"], "away": comp["AWAY"], "start": start,
                    "league": lg.get("name", ""), "markets": mk, "bid": int(e["id"]), "sk": sk})
    return out


def leon_fetch(cfg):
    """Матчи Леона выбранных видов спорта: список лиг -> матчи каждой лиги. -> список событий (сырых)."""
    try:
        sports = _leon_req(cfg, "/api-2/betline/sports?flags=urlv2", timeout=25)
    except Exception as e:
        LEON_CACHE["pause"] = time.time() + 300
        log("Леон недоступен с этого подключения: %s: %s (следующая попытка через 5 минут)" % (type(e).__name__, e))
        return []
    leagues = []
    for sp in sports:
        sk = LEON_FAM.get(sp.get("family"))
        if sk not in cfg["leon_sports"]:
            continue
        ls = [l for r in sp.get("regions") or [] for l in r.get("leagues") or []
              if (l.get("prematch") or 0) > 0 and not FAKE_LEAGUE.search(l.get("name", ""))]
        if sk == "esports":
            ls = [l for r in sp.get("regions") or [] for l in r.get("leagues") or [] if (l.get("prematch") or 0) > 0]
        ls.sort(key=lambda l: -(l.get("weight") or 0))
        leagues += [l["id"] for l in ls[:cfg["leon_max_leagues"]]]
        for l in ls[:cfg["leon_max_leagues"]]:
            LEON_LG[l["id"]] = {"id": l["id"], "name": l.get("name", ""), "sport": {"family": sp.get("family"), "name": sp.get("name", "")}}
    log("Леон: лиг с матчами %d" % len(leagues))
    out, lock, queue = [], threading.Lock(), list(leagues)
    t_end = time.time() + cfg["leon_budget"]

    def runner():
        while True:
            with lock:
                if not queue or time.time() > t_end:
                    return
                lid = queue.pop(0)
            try:
                r = _leon_req(cfg, "/api-2/betline/events/all?league_id=%d&hideClosed=true&flags=%s" % (lid, LEON_FLAGS), timeout=40)
                evs = r.get("events") or []
                for e in evs:                                   # режим nodup: у повторных матчей лиги данные о лиге опущены — достраиваем
                    lg = e.get("league") or {}
                    if not (lg.get("sport") or {}).get("family") or not lg.get("name"):
                        e["league"] = dict(LEON_LG.get(lid) or lg)
                with lock:
                    out.extend(evs)
            except Exception as e:
                log("Леон: лига %s: %s: %s" % (lid, type(e).__name__, e))
    ths = [threading.Thread(target=runner, daemon=True) for _ in range(max(1, int(cfg["leon_threads"])))]
    for t in ths:
        t.start()
    for t in ths:
        t.join()
    log("Леон: лиг %d, не обработано %d, матчей %d" % (len(leagues), len(queue), len(out)))
    return out


def leon_events(raw, now=None):
    out, seen = [], set()
    for ev in leon_parse(raw, now):
        if ev["bid"] not in seen:
            seen.add(ev["bid"])
            out.append(ev)
    return out


def add_leon_details(cfg, pairs):
    """Для ближайших совпавших матчей запрашиваем страницу матча: все линии, угловые, тайм, ДШ, обе забьют, ИТ."""
    cand = sorted(pairs, key=lambda p: p[0]["start"])[:cfg["leon_detail_max"]]
    lock, queue, done = threading.Lock(), list(cand), [0]

    def runner():
        while True:
            with lock:
                if not queue:
                    return
                w = queue.pop(0)[0]
            try:
                r = _leon_req(cfg, "/api-2/betline/event/all?eventId=%d&flags=%s" % (w["bid"], LEON_FLAGS_FULL), timeout=40)
                w["markets"].update(leon_markets(r.get("markets"), w["sk"]))
                with lock:
                    done[0] += 1
            except Exception as e:
                log("Леон: страница матча %s: %s: %s" % (w.get("bid"), type(e).__name__, e))
    ths = [threading.Thread(target=runner, daemon=True) for _ in range(max(1, int(cfg["leon_threads"])))]
    for t in ths:
        t.start()
    for t in ths:
        t.join()
    log("Леон: страницы матчей %d из %d" % (done[0], len(cand)))


def load_leon_har(path):
    """Дамп браузера -> (сырые события со списков лиг, {eventId: рынки страницы матча})."""
    with open(path, encoding="utf-8") as fh:
        h = json.load(fh)
    evs, pages = [], {}
    for e in h["log"]["entries"]:
        u = e["request"]["url"]
        c = e["response"]["content"]
        t = c.get("text") or ""
        if "leon.ru/api-2/betline/" not in u or not t:
            continue
        if c.get("encoding") == "base64":
            t = base64.b64decode(t).decode("utf-8", "replace")
        try:
            r = json.loads(t)
        except ValueError:
            continue
        if "/betline/events/all" in u or "/betline/changes/all" in u or "/betline/related/all" in u:
            evs += r.get("events") or r.get("data") or []
        elif "/betline/headline-matches" in u:
            evs += (r.get("events") or {}).get("events") or []
        elif "/betline/event/all" in u and isinstance(r, dict) and r.get("markets"):
            pages[int(r["id"])] = r["markets"]
            evs.append(r)
    return evs, pages


# ============================================================ Лига Ставок (JSON по HTTPS, lds-api.ligastavok.ru)
#   POST /rest/events/v8/eventsList  {"gameId":[вид спорта],"limit":N,"offset":M,"topEvents":false,"view":"priority"} — матчи с основными рынками
#   POST /rest/events/v6/actionLine  {"id":<id матча>}  — страница матча: все рынки (много линий, тайм, угловые)
#   рынок: type (WIN / WIN2 / DBL / HAN / TTL / BTSR / ITL1 / ITL2), partId -> parts[partId].code (период), outcomes: value (кф), adValue (линия)
#   HAN: исход "1" с adValue = линия хозяев; TTL: "less" / "gross"; ITL: «Мен» / «Бол»
LS_HOST = "https://lds-api.ligastavok.ru"
LS_GAMES = {33: "football", 31: "hockey", 34: "tennis", 25: "basketball", 128: "volleyball", 1246: "table-tennis",
            30: "handball", 24: "baseball", 7486: "rugby", 23: "am-football", 355: "waterpolo", 1445: "aussie-rules",
            10014: "esports"}
# какие части матча берём: код части -> (префикс ключа, брать исходы, брать форы и тоталы)
_LS_FULL = {"FULLTIME": ("", True, True)}
LS_PARTS = {
    "football": {"FULLTIME": ("", True, True), "HALFTIME_1": ("1H:", True, True), "HALFTIME_2": ("2H:", True, True),
                 "CORNERS-FULLTIME": ("CRN:", False, True), "CORNERS-HALFTIME_1": ("1H:CRN:", False, True),
                 "CORNERS-HALFTIME_2": ("2H:CRN:", False, True)},
    "hockey": _LS_FULL, "handball": _LS_FULL, "rugby": _LS_FULL, "waterpolo": _LS_FULL, "baseball": _LS_FULL,
    "basketball": {"OVERALLTIME": ("", True, True)}, "am-football": {"OVERALLTIME": ("", True, True)},
    "aussie-rules": {"OVERALLTIME": ("", True, True)},
    "tennis": {"OVERALLTIME": ("", True, False), "GAME-OVERALLTIME": ("", False, True)},
    "volleyball": {"OVERALLTIME": ("", True, False), "POINT-OVERALLTIME": ("", False, True)},
    "table-tennis": {"OVERALLTIME": ("", True, False), "POINT-OVERALLTIME": ("", False, True)},
    "esports": {"OVERALLTIME": ("", True, True)},     # киберспорт: победитель матча, фора и тотал ПО КАРТАМ (киллы и раунды не берём)
}
LS_CACHE = {"t": 0.0, "ev": [], "fails": 0, "detail": {}}
LS_RATE = {"next": 0.0, "gap": None}
LS_LOCK = threading.Lock()


def _ls_post(cfg, path, body, timeout=40):
    """POST JSON -> поле result. Дополнительные заголовки (если сайт их требует) — cfg["ls_headers"]."""
    _ls_throttle(cfg)
    # Заголовки мобильного Chrome, как у сайта для гостя (из дампа с телефона): без токенов аккаунта API отвечает 200
    headers = {"User-Agent": "Mozilla/5.0 (Linux; Android 10; K) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/157.0.0.0 Mobile Safari/537.36",
               "Accept": "application/json", "Content-Type": "application/json",
               "Accept-Language": "ru-RU,ru;q=0.9,en-US;q=0.8,en;q=0.7", "Origin": "https://www.ligastavok.ru",
               "Referer": "https://www.ligastavok.ru/", "Country-Code": "RUS", "Locale": "ru-RU", "x-application-name": "mobile",
               "x-req-id": str(uuid.uuid4()), "sec-fetch-dest": "empty", "sec-fetch-mode": "cors", "sec-fetch-site": "same-site",
               "sec-ch-ua": '"Not-A.Brand";v="99", "Google Chrome";v="157", "Chromium";v="157"', "sec-ch-ua-mobile": "?1",
               "sec-ch-ua-platform": '"Android"'}
    if not cfg.get("ls_anon", True):
        headers.update(cfg.get("ls_headers") or {})
    for k in cfg.get("ls_drop_headers") or []:
        headers.pop(k, None)
    data = json.dumps(body)
    url = LS_HOST + path
    if cfg.get("ls_curl", True) and shutil.which("curl"):
        last = None
        for curves in (["--curves", "X25519"], []):
            cmd = ["curl", "-4", "-sS", "--compressed", "-m", str(int(timeout)), "--connect-timeout", "10",
                   "-w", "\n%{http_code}", "-X", "POST", "--data-raw", data] + curves
            if os.environ.get("ARB_CURL_INSECURE"):
                cmd.append("-k")
            for k, v in headers.items():
                cmd += ["-H", "%s: %s" % (k, v)]
            cmd.append(url)
            res = subprocess.run(cmd, capture_output=True, timeout=timeout + 10)
            if res.returncode == 0:
                txt, _, code = res.stdout.decode("utf-8", "replace").rpartition("\n")
                return _ls_result(code, txt)
            last = OSError("curl %d: %s" % (res.returncode, res.stderr.decode("utf-8", "replace").strip()[:200]))
            if res.returncode not in (28, 35, 7):
                break
        raise last
    req = urllib.request.Request(url, data=data.encode(), headers=dict(headers, **{"Accept-Encoding": "gzip"}))
    try:
        with _BC_OPENER.open(req, timeout=timeout) as r:
            raw, code = r.read(), str(r.status)
            if (r.headers.get("Content-Encoding") or "").lower() == "gzip":
                raw = gzip.decompress(raw)
    except urllib.error.HTTPError as e:
        raw, code = e.read(), str(e.code)
    return _ls_result(code, raw.decode("utf-8", "replace"))


def _ls_result(code, txt):
    if code != "200":
        raise OSError("Лига Ставок ответила HTTP %s: %s" % (code, re.sub(r"\s+", " ", re.sub(r"<[^>]+>", " ", txt))[:160]))
    try:
        d = json.loads(txt)
    except ValueError:
        raise OSError("Лига Ставок ответила не JSON: %s" % txt[:120])
    if d.get("error"):
        raise OSError("Лига Ставок: ошибка %s" % json.dumps(d["error"], ensure_ascii=False)[:160])
    return d.get("result")


def _ls_throttle(cfg):
    base = float(cfg["ls_gap"])
    with LS_LOCK:
        gap = LS_RATE["gap"] or base
        now = time.time()
        wait = max(0.0, LS_RATE["next"] - now)
        LS_RATE["next"] = max(now, LS_RATE["next"]) + gap * random.uniform(0.8, 1.3)
    if wait:
        time.sleep(wait)


def _ls_ok(cfg):
    with LS_LOCK:
        LS_CACHE["fails"] = 0
        LS_CACHE["notified"] = 0
        g = LS_RATE["gap"]
        if g and g > float(cfg["ls_gap"]):
            LS_RATE["gap"] = max(float(cfg["ls_gap"]), g * 0.9)


def _ls_fail(cfg, what):
    with LS_LOCK:
        LS_CACHE["fails"] += 1
        n = LS_CACHE["fails"]
        LS_RATE["gap"] = min(12.0, (LS_RATE["gap"] or float(cfg["ls_gap"])) * 1.5)
        LS_CACHE["pause"] = time.time() + (1200 if re.search(r"curl (28|35|7)\b|HTTP (403|429)\b", what) else min(900, 60 * 2 ** (n - 1)))
        wait = LS_CACHE["pause"] - time.time()
    log("Лига Ставок: %s — пауза %d с" % (what, wait))
    if cfg.get("ls_anon", True) and re.search(r"curl (28|35|7)\b|HTTP (403|429)\b", what):
        notify_block(cfg, "ligastavok", "Лига Ставок")
    if ("HTTP 401" in what or "HTTP 403" in what) and n >= 3 and cfg.get("ls_headers") and not cfg.get("ls_anon", True) and time.time() - LS_CACHE.get("notified", 0) > 6 * 3600:
        LS_CACHE["notified"] = time.time()
        saved = cfg.get("ls_token_saved")
        age = (" (токен получен %.1f ч назад)" % ((time.time() - saved) / 3600)) if saved else ""
        try:
            tg_send(cfg, "⚠️ Лига Ставок перестала отвечать: токен устарел%s.\nОбновите: снимите новый HAR на ligastavok.ru (войдя в аккаунт), "
                         "отправьте на телефон и выполните: python arbphone.py --ls-har ~/downloads/*ligastavok*.har, затем перезапустите бота." % age)
        except Exception:
            pass


def _ls_line(s):
    try:
        v = float(s)
    except (TypeError, ValueError):
        return None
    return v if (v * 2) == int(v * 2) else None                 # четвертные линии не берём


def ls_markets(ev, sk):
    """Рынки матча Лиги Ставок -> рынки в нашем виде. Закрытые рынки и исходы пропускаем."""
    parts = LS_PARTS.get(sk)
    if not parts:
        return {}
    pmap = {}
    for pid, p in (ev.get("parts") or {}).items():
        if p.get("code") in parts and not p.get("locked") and not p.get("corrupted"):
            pmap[pid] = parts[p["code"]]
    by = collections.defaultdict(list)
    for o in (ev.get("outcomes") or {}).values():
        if not o.get("locked") and not o.get("corrupted") and (o.get("value") or 0) > 1:
            by[o.get("marketId")].append(o)
    mk = {}
    for k, m in (ev.get("markets") or {}).items():
        sel = pmap.get(m.get("partId"))
        if not sel or m.get("locked") or m.get("corrupted"):
            continue
        pre, wins, lines = sel
        typ, title = m.get("type"), m.get("title") or ""
        os_ = by.get(k) or []
        if not os_:
            continue
        if sk == "esports" and title not in ("Победитель", "Фора по картам", "Тотал по картам"):
            continue
        if typ in ("WIN", "WIN2") and wins and title == "Победитель":
            d = {o["title"]: o["value"] for o in os_}
            if "1" in d and "2" in d:
                if "X" in d:
                    mk.setdefault(pre + "1X2", {"1": d["1"], "X": d["X"], "2": d["2"]})
                elif not pre:
                    mk.setdefault("ML", {"1": d["1"], "2": d["2"]})
        elif typ == "DBL" and wins and sk == "football":
            d = {o["title"]: o["value"] for o in os_}
            if all(x in d for x in ("1X", "12", "X2")):
                mk.setdefault(pre + "DC", {"1X": d["1X"], "12": d["12"], "X2": d["X2"]})
        elif typ == "BTSR" and wins and sk == "football" and title == "Обе забьют":
            d = {o["outcomeKey"]: o["value"] for o in os_}
            if "yes" in d and "no" in d:
                mk.setdefault(pre + "BTTS", {"Y": d["yes"], "N": d["no"]})
        elif typ == "HAN" and lines:
            d = {o["title"]: o for o in os_}
            if "1" in d and "2" in d:
                h = _ls_line(d["1"].get("adValue"))
                if h is not None and _ls_line(d["2"].get("adValue")) == -h:
                    mk.setdefault("%sHCP:%.2f" % (pre, h + 0.0), {"1": d["1"]["value"], "2": d["2"]["value"]})
        elif typ == "TTL" and lines and title == "Тотал":
            d = {o["outcomeKey"]: o for o in os_}
            if "less" in d and "gross" in d:
                t = _ls_line(d["gross"].get("adValue"))
                if t is not None and _ls_line(d["less"].get("adValue")) == t:
                    mk.setdefault("%sTOTAL:%.2f" % (pre, t), {"O": d["gross"]["value"], "U": d["less"]["value"]})
        elif typ in ("ITL1", "ITL2") and lines and sk == "football":
            d = {o["title"]: o for o in os_}
            if "Мен" in d and "Бол" in d:
                t = _ls_line(d["Бол"].get("adValue"))
                if t is not None and _ls_line(d["Мен"].get("adValue")) == t:
                    mk.setdefault("%s%s:%.2f" % (pre, "IT1" if typ == "ITL1" else "IT2", t), {"O": d["Бол"]["value"], "U": d["Мен"]["value"]})
    return mk


def ls_parse(items, now=None):
    """Матчи eventsList -> [{bk, home, away, start, league, markets, bid, sk}] (только прематч)."""
    now = now or time.time()
    out = []
    for x in items or []:
        sk = LS_GAMES.get(x.get("gameId"))
        e = x.get("event") or {}
        if not sk or x.get("ns") != "prematch" or not e.get("team1") or not e.get("team2"):
            continue
        lg = "%s %s" % (e.get("topicTitle") or "", e.get("tournamentTitle") or "")
        if FAKE_LEAGUE.search(lg):
            continue
        start = int((x.get("gameTs") or 0) / 1000)
        if start < now:
            continue
        out.append({"bk": "ligastavok", "home": e["team1"], "away": e["team2"], "start": start,
                    "league": (e.get("topicTitle") or e.get("tournamentTitle") or ""), "markets": ls_markets(x, sk),
                    "bid": int(x["id"]), "sk": sk})
    return out


def ls_fetch(cfg):
    """Матчи Лиги Ставок по видам спорта. Сайт отдаёт до 40 матчей за запрос, поэтому листаем (exceptEventIds), а виды спорта
    обновляем по очереди: каждый цикл — самые давно не обновлявшиеся; накопленное хранится ls_max_age секунд. -> список сырых матчей."""
    now = time.time()
    by = LS_CACHE.setdefault("by_sport", {})
    if now >= LS_CACHE.get("pause", 0):
        t_end = now + cfg["ls_budget"]
        order = sorted((g for g, sk in LS_GAMES.items() if sk in cfg["ls_sports"]), key=lambda g: by.get(g, (0, []))[0])
        for gid in order:
            if time.time() > t_end or time.time() - by.get(gid, (0, []))[0] < cfg["ls_refresh"]:
                continue
            got, seen = [], []
            while time.time() < t_end:
                body = {"gameId": [gid], "limit": int(cfg["ls_limit"]), "topEvents": False, "view": "priority"}
                if seen:
                    body["exceptEventIds"] = seen                  # как на сайте: уже полученные матчи исключаем, получаем следующие
                try:
                    r = _ls_post(cfg, "/rest/events/v8/eventsList", body)
                except Exception as e:
                    _ls_fail(cfg, "%s: %s: %s" % (LS_GAMES[gid], type(e).__name__, e))
                    break
                _ls_ok(cfg)
                data = (r or {}).get("data") or []
                total = (r or {}).get("total")
                for x in data:
                    seen.append(x["id"])
                got += data
                if not data or (total is not None and len(seen) >= total) or len(seen) >= cfg["ls_max_events"]:
                    break
            if got:
                by[gid] = (time.time(), got)
            if time.time() < LS_CACHE.get("pause", 0):
                break
    raw, ids = [], set()
    for gid, (t, items) in list(by.items()):
        if now - t > cfg["ls_max_age"] and time.time() - t > cfg["ls_max_age"]:
            del by[gid]
            continue
        for x in items:
            if x["id"] not in ids:
                ids.add(x["id"])
                raw.append(x)
    LS_CACHE["raw"] = raw
    LS_CACHE["t"] = min((t for t, _ in by.values()), default=0.0)
    log("Лига Ставок: матчей %d (видов спорта в запасе %d)" % (len(raw), len(by)))
    return raw


def ls_events(raw, now=None):
    out, seen = [], set()
    for ev in ls_parse(raw, now):
        if ev["bid"] not in seen:
            seen.add(ev["bid"])
            out.append(ev)
    return out


def add_ls_details(cfg, pairs):
    """Страница матча (все линии, тайм, угловые) — для ближайших совпавших матчей, понемногу за цикл; хранится ls_detail_ttl секунд."""
    det = LS_CACHE["detail"]
    cand = sorted(pairs, key=lambda p: p[0]["start"])[:cfg["ls_detail_max"]]
    now, fetched, left = time.time(), 0, 0
    for w, f, sw in cand:
        c = det.get(w["bid"])
        if not c or now - c[0] > cfg["ls_detail_ttl"]:
            if fetched >= cfg["ls_detail_per_cycle"] or time.time() < LS_CACHE.get("pause", 0):
                left += 1
            else:
                try:
                    r = _ls_post(cfg, "/rest/events/v6/actionLine", {"id": w["bid"]})
                    c = det[w["bid"]] = (time.time(), ls_markets(r or {}, w["sk"]))
                    fetched += 1
                    _ls_ok(cfg)
                except Exception as e:
                    _ls_fail(cfg, "страница матча %s: %s: %s" % (w.get("bid"), type(e).__name__, e))
                    left += 1
                    c = det.get(w["bid"])
        if c:
            w["markets"].update(c[1])
    for b in [b for b, (t, _) in det.items() if now - t > cfg["ls_detail_ttl"] * 3]:
        del det[b]
    if fetched or left:
        log("Лига Ставок: страницы матчей обновлено %d, ждут очереди %d из %d" % (fetched, left, len(cand)))


# ============================================================ Олимп (JSON по HTTPS, www.olimp.bet/api/v4/0/line, вход не нужен)
#   GET /line/sports-with-competitions-with-events?vids[]=<вид спорта>:  — все матчи вида спорта с основными рынками
#   GET /line/events?vids[]=<id матча>:&main=false                       — страница матча: все рынки
#   исход: marketId (1 — 1X2, 2 / 4366 / 67 — победитель, 3 — двойной шанс, 4 — фора, 5 — тотал, 7 / 8 — инд. тотал, 30 — обе забьют,
#   10–15 — тайм), shortName (П1 / Х / П2 / Фора 1 / ТотМ / ТотБ …), param (линия), probability (кф)
OL_HOST = "https://www.olimp.bet"
OL_SPORTS = {"1": "football", "2": "hockey", "3": "tennis", "5": "basketball", "10": "volleyball", "40": "table-tennis",
             "9": "handball", "29": "baseball", "6": "am-football", "46": "rugby", "41": "waterpolo", "91": "aussie-rules", "112": "esports"}
OL_CACHE = {"t": 0.0, "fails": 0, "pause": 0.0, "detail": {}, "by_sport": {}, "guid": uuid.uuid4().hex}
OL_RATE = {"next": 0.0, "tok": None, "tok_t": 0.0}
OL_LOCK = threading.Lock()
_OL_MIN_TOTAL = {"tennis": 8.5, "table-tennis": 20.0, "volleyball": 60.0}      # меньшие линии — тоталы в сетах/партиях, не берём
_OL_MIN_HCP = {"tennis": 2.5, "table-tennis": 3.5, "volleyball": 5.0}           # малые форы — в сетах, не берём
_OL_PER3 = {10: "1H:", 13: "2H:"}
_OL_PERDC = {112: "1H:", 113: "2H:"}
_OL_PERHCP = {11: "1H:", 14: "2H:"}
_OL_PERTOT = {12: "1H:", 15: "2H:"}
_OL_IT = {7: "IT1", 8: "IT2", 43: "1H:IT1", 44: "1H:IT2", 45: "2H:IT1", 46: "2H:IT2"}
_OL_BTTS = {30: "BTTS", 191: "1H:BTTS", 192: "2H:BTTS"}


def _ol_throttle(cfg):
    """Пауза между запросами + «ведро» (olimp_burst запросов подряд, потом olimp_per_min в минуту); после блокировки ведро пустое."""
    with OL_LOCK:
        now = time.time()
        wait = max(0.0, OL_RATE["next"] - now)
        OL_RATE["next"] = max(now, OL_RATE["next"]) + float(cfg["olimp_gap"]) * random.uniform(0.9, 1.3)
        cap, rate = float(cfg["olimp_burst"]), float(cfg["olimp_per_min"]) / 60.0
        if OL_RATE["tok"] is None:
            OL_RATE["tok"], OL_RATE["tok_t"] = float(cfg["olimp_burst_start"]), now
        tok = min(cap, OL_RATE["tok"] + max(0.0, now - OL_RATE["tok_t"]) * rate)
        if tok < 1:
            wait = max(wait, (1 - tok) / rate)
            tok = 1.0
        OL_RATE["tok"], OL_RATE["tok_t"] = tok - 1.0, now + wait
    if wait:
        time.sleep(wait)


def _ol_req(cfg, path, timeout=60):
    """GET JSON. Заголовки как у сайта (accept, referer, user-agent, x-guid); через curl, если он есть."""
    _ol_throttle(cfg)
    url = OL_HOST + path
    headers = {"User-Agent": LEON_UA, "Accept": "application/json", "Accept-Language": "ru,en;q=0.9", "Referer": "https://www.olimp.bet/line",
               "Origin": "https://www.olimp.bet", "x-guid": OL_CACHE["guid"], "sec-fetch-dest": "empty", "sec-fetch-mode": "cors",
               "sec-fetch-site": "same-origin"}
    if cfg.get("olimp_curl", True) and shutil.which("curl"):
        last = None
        for curves in (["--curves", "X25519"], []):
            cmd = ["curl", "-4", "-sS", "--compressed", "-m", str(int(timeout)), "--connect-timeout", "15", "-w", "\n%{http_code}"] + curves
            if os.environ.get("ARB_CURL_INSECURE"):
                cmd.append("-k")
            for k, v in headers.items():
                cmd += ["-H", "%s: %s" % (k, v)]
            cmd.append(url)
            res = subprocess.run(cmd, capture_output=True, timeout=timeout + 10)
            if res.returncode == 0:
                body, _, code = res.stdout.decode("utf-8", "replace").rpartition("\n")
                if code != "200":
                    raise OSError("Олимп ответил HTTP %s: %s" % (code, re.sub(r"\s+", " ", re.sub(r"<[^>]+>", " ", body))[:120]))
                return json.loads(body)
            last = OSError("curl %d: %s" % (res.returncode, res.stderr.decode("utf-8", "replace").strip()[:200]))
            if res.returncode not in (28, 35, 7):
                break
        raise last
    req = urllib.request.Request(url, headers=dict(headers, **{"Accept-Encoding": "gzip"}))
    with urllib.request.urlopen(req, timeout=timeout) as r:
        raw = r.read()
        if (r.headers.get("Content-Encoding") or "").lower() == "gzip":
            raw = gzip.decompress(raw)
    return json.loads(raw.decode("utf-8", "replace"))


def _ol_line(x):
    try:
        v = float(x)
    except (TypeError, ValueError):
        return None
    return v if (v * 2) == int(v * 2) else None                 # четвертные линии (x.25 / x.75) не берём


def olimp_markets(outs, sk):
    """Исходы матча Олимпа -> рынки в нашем виде. Тайм-рынки и индивидуальные тоталы — только футбол."""
    foot = sk == "football"
    mk = {}
    w3, dc, hcp, tot, itl, btts = {}, {}, {}, {}, {}, {}
    for o in outs or []:
        try:
            c = float(o.get("probability"))
        except (TypeError, ValueError):
            continue
        if c <= 1.0:
            continue
        mid, sn, nm, par = o.get("marketId"), o.get("shortName") or "", o.get("unprocessedName") or "", o.get("param")
        if mid == 1 and sk != "basketball" and sn in ("П1", "Х", "П2"):
            w3.setdefault("", {})[{"П1": "1", "Х": "X", "П2": "2"}[sn]] = c
        elif foot and mid in _OL_PER3:
            k = "1" if nm.startswith("П1") else "2" if nm.startswith("П2") else "X" if nm[:1] in ("Х", "X") else None
            if k:
                w3.setdefault(_OL_PER3[mid], {})[k] = c
        elif mid == 3 and sk != "basketball" and sn in ("1Х", "12", "Х2"):
            dc.setdefault("", {})[sn.replace("Х", "X")] = c
        elif foot and mid in _OL_PERDC:
            k = nm[:2].replace("Х", "X").replace("x", "X")
            if k in ("1X", "12", "X2"):
                dc.setdefault(_OL_PERDC[mid], {})[k] = c
        elif mid in (2, 4366, 67) and not foot and sn in ("П1", "П2", "П1м", "П2м"):
            mk.setdefault("ML", {})["1" if sn.startswith("П1") else "2"] = c
        elif mid == 4 or (foot and mid in _OL_PERHCP):
            pre = _OL_PERHCP.get(mid, "") if mid != 4 else ""
            m = re.search(r"Ф(?:ора )?([12])", sn)
            h = _ol_line(par)
            if m and h is not None:
                team = m.group(1)
                line = h if team == "1" else -h
                if abs(line) >= _OL_MIN_HCP.get(sk, 0):
                    hcp.setdefault((pre, line), {})[team] = c
        elif mid == 5 or (foot and mid in _OL_PERTOT):
            pre = _OL_PERTOT.get(mid, "") if mid != 5 else ""
            t = _ol_line(par)
            if t is not None and t >= _OL_MIN_TOTAL.get(sk, 0):
                side = "U" if "мен" in nm else "O" if "бол" in nm else None
                if side:
                    tot.setdefault((pre, t), {})[side] = c
        elif foot and mid in _OL_IT:
            t = _ol_line(par)
            side = "U" if "мен" in nm else "O" if "бол" in nm else None
            if t is not None and side:
                itl.setdefault((_OL_IT[mid], t), {})[side] = c
        elif foot and mid in _OL_BTTS:
            side = "Y" if nm.endswith("да") else "N" if nm.endswith("нет") else None
            if side:
                btts.setdefault(_OL_BTTS[mid], {})[side] = c
    for pre, d in w3.items():
        if len(d) == 3:
            mk[pre + "1X2"] = d
    for pre, d in dc.items():
        if len(d) == 3:
            mk[pre + "DC"] = d
    for (pre, h), d in hcp.items():
        if len(d) == 2:
            mk["%sHCP:%.2f" % (pre, h + 0.0)] = d
    for (pre, t), d in tot.items():
        if len(d) == 2:
            mk["%sTOTAL:%.2f" % (pre, t)] = {"O": d["O"], "U": d["U"]}
    for (k, t), d in itl.items():
        if len(d) == 2:
            pre = k[:-3]
            mk["%s%s:%.2f" % (pre, k[-3:], t)] = {"O": d["O"], "U": d["U"]}
    for k, d in btts.items():
        if len(d) == 2:
            mk[k] = d
    if "ML" in mk and len(mk["ML"]) != 2:
        del mk["ML"]
    return mk


def olimp_walk(j):
    """Ответ списка (sports-with-competitions-with-events или competitions-with-events) -> матчи."""
    for x in j or []:
        pl = x.get("payload") or {}
        for c in (pl.get("competitionsWithEvents") or [pl]):
            for ev in c.get("events") or []:
                yield ev


def olimp_parse(j, now=None, until=None):
    """-> [{bk, home, away, start, league, markets, bid, sk}] (только прематч; until — не позже этого времени)."""
    now = now or time.time()
    out = []
    for ev in olimp_walk(j):
        sk = OL_SPORTS.get(str(ev.get("sportId")))
        if not sk or ev.get("state") not in (None, "OPEN") or not ev.get("team1Name") or not ev.get("team2Name"):
            continue
        lg = ev.get("competitionName") or ""
        if FAKE_LEAGUE.search(lg):
            continue
        start = int(ev.get("startDateTime") or 0)
        if start < now or (until and start > until):
            continue
        out.append({"bk": "olimp", "home": ev["team1Name"], "away": ev["team2Name"], "start": start, "league": lg,
                    "markets": olimp_markets(ev.get("outcomes"), sk), "bid": int(ev["id"]), "sk": sk})
    return out


def _ol_ok(cfg):
    with OL_LOCK:
        OL_CACHE["fails"] = 0
        was = OL_CACHE.get("blocked")
        OL_CACHE["blocked"] = False
        if was:
            OL_RATE["tok"], OL_RATE["tok_t"] = 0.0, time.time() + 300      # после снятия блока — осторожно: 5 минут без серий запросов
    if was:
        log("Олимп: доступ восстановлен, продолжаю осторожно")
        tg_send(cfg, "✅ Олимп снова доступен — бот продолжил собирать матчи.")


def _ol_is_block(what):
    """Блокировка адреса: обрыв/таймаут подключения (curl 28/7/35) или HTTP 403/429."""
    return bool(re.search(r"curl (28|7|35|52|56)\b|HTTP (403|429)\b|timed out|Connection (refused|reset)", what))


def _ol_fail(cfg, what):
    """Ошибка запроса. Блокировка адреса: долгая пауза olimp_block_pause (сайт держал блок 1,5 часа и больше), потом одна проба
    самого лёгкого запроса; не прошла — следующая проба через olimp_probe_pause. Прочие ошибки — короткая растущая пауза."""
    notify = False
    with OL_LOCK:
        OL_CACHE["fails"] += 1
        n = OL_CACHE["fails"]
        if _ol_is_block(what):
            if not OL_CACHE.get("blocked"):
                OL_CACHE["blocked"] = True
                pause = float(cfg["olimp_block_pause"])
                notify = True
            else:
                pause = float(cfg["olimp_probe_pause"])
            OL_RATE["tok"], OL_RATE["tok_t"] = 0.0, time.time() + pause
        else:
            pause = min(900, 45 * 2 ** (n - 1))
        OL_CACHE["pause"] = time.time() + pause
    log("Олимп: %s — пауза %d с%s" % (what, pause, " (блокировка адреса)" if _ol_is_block(what) else ""))
    if notify:
        notify_block(cfg, "olimp", "Олимп")


def olimp_fetch(cfg):
    """Матчи Олимпа: по запросу на вид спорта, виды спорта обновляем по очереди (самые давно не обновлявшиеся первыми);
    накопленное хранится olimp_max_age секунд. -> список матчей (уже разобранных)."""
    now = time.time()
    by = OL_CACHE["by_sport"]
    if now >= OL_CACHE["pause"]:
        t_end = now + cfg["olimp_budget"]
        order = sorted((i for i, sk in OL_SPORTS.items() if sk in cfg["olimp_sports"]),
                       key=lambda i: (0 if (OL_CACHE.get("blocked") and i == "3") else 1, by.get(i, (0, []))[0]))   # после блока — первой проба лёгким запросом (теннис)
        for sid in order:
            refresh = cfg["olimp_refresh_football"] if sid == "1" else cfg["olimp_refresh"]
            if time.time() > t_end or time.time() - by.get(sid, (0, []))[0] < refresh:
                continue
            try:
                j = _ol_req(cfg, "/api/v4/0/line/sports-with-competitions-with-events?vids%%5B%%5D=%s%%3A" % sid, timeout=90)
                evs = olimp_parse(j, until=(time.time() + cfg["horizon_hours"] * 3600) if cfg.get("horizon_hours") else None)
                del j
            except Exception as e:
                _ol_fail(cfg, "%s: %s: %s" % (OL_SPORTS[sid], type(e).__name__, e))
                break
            _ol_ok(cfg)
            by[sid] = (time.time(), evs)
    out, ids = [], set()
    t0 = 0.0
    for sid, (t, evs) in list(by.items()):
        if time.time() - t > cfg["olimp_max_age"]:
            del by[sid]
            continue
        t0 = t if not t0 else min(t0, t)
        for e in evs:
            if e["bid"] not in ids and e["start"] > now:
                ids.add(e["bid"])
                out.append(e)
    OL_CACHE["t"] = t0
    log("Олимп: матчей %d (видов спорта в запасе %d)" % (len(out), len(by)))
    return out


def add_olimp_details(cfg, pairs):
    """Страница матча (все линии, тайм) — для ближайших совпавших матчей, понемногу за цикл; хранится olimp_detail_ttl секунд."""
    det = OL_CACHE["detail"]
    cand = sorted(pairs, key=lambda p: p[0]["start"])[:cfg["olimp_detail_max"]]
    now, fetched, left = time.time(), 0, 0
    for w, f, sw in cand:
        c = det.get(w["bid"])
        if not c or now - c[0] > cfg["olimp_detail_ttl"]:
            if fetched >= cfg["olimp_detail_per_cycle"] or time.time() < OL_CACHE["pause"]:
                left += 1
            else:
                try:
                    r = _ol_req(cfg, "/api/v4/0/line/events?vids%%5B%%5D=%s%%3A&main=false" % w["bid"], timeout=40)
                    outs = []
                    for x in r or []:
                        outs += (x.get("payload") or {}).get("outcomes") or []
                    c = det[w["bid"]] = (time.time(), olimp_markets(outs, w["sk"]))
                    fetched += 1
                    _ol_ok(cfg)
                except Exception as e:
                    _ol_fail(cfg, "страница матча %s: %s: %s" % (w.get("bid"), type(e).__name__, e))
                    left += 1
                    c = det.get(w["bid"])
        if c:
            w["markets"].update(c[1])
    for b in [b for b, (t, _) in det.items() if now - t > cfg["olimp_detail_ttl"] * 3]:
        del det[b]
    if fetched or left:
        log("Олимп: страницы матчей обновлено %d, ждут очереди %d из %d" % (fetched, left, len(cand)))


def load_olimp_har(path):
    """Дамп браузера Олимпа -> (ответы списков, {id матча: исходы страницы})."""
    with open(path, encoding="utf-8") as fh:
        h = json.load(fh)
    lists, pages = [], {}
    for e in h["log"]["entries"]:
        u, t = e["request"]["url"], (e["response"]["content"] or {}).get("text") or ""
        if "olimp.bet/api/v4/0/line/" not in u or not t:
            continue
        try:
            j = json.loads(t)
        except ValueError:
            continue
        if "/line/events?" in u:
            for x in j:
                pl = x.get("payload") or {}
                if pl.get("outcomes"):
                    pages[int(pl["id"])] = pl["outcomes"]
        elif "competitions-with-events" in u:
            lists.append(j)
    return lists, pages


def olimp_test(cfg):
    """python arbphone.py --olimp-test : проверка Олимпа — список матчей футбола и страница одного матча."""
    t = time.time()
    try:
        j = _ol_req(cfg, "/api/v4/0/line/sports-with-categories-with-competitions?vids%5B%5D=", timeout=40)
    except Exception as e:
        print("1. дерево турниров: ОШИБКА %s: %s" % (type(e).__name__, e))
        return
    print("1. дерево турниров: %.1f с, видов спорта %d" % (time.time() - t, len(j or [])))
    t = time.time()
    try:
        j = _ol_req(cfg, "/api/v4/0/line/sports-with-competitions-with-events?vids%5B%5D=3%3A", timeout=60)
    except Exception as e:
        print("2. теннис: ОШИБКА %s: %s" % (type(e).__name__, e))
        return
    evs = olimp_parse(j)
    print("2. теннис: %.1f с, матчей %d, с рынками %d" % (time.time() - t, len(evs), sum(1 for e in evs if e["markets"])))
    for e in evs[:3]:
        print("   -", e["home"], "-", e["away"], time.strftime("%d.%m %H:%M", time.gmtime(e["start"] + 3 * 3600)), sorted(e["markets"])[:8])
    if evs:
        t = time.time()
        r = _ol_req(cfg, "/api/v4/0/line/events?vids%%5B%%5D=%s%%3A&main=false" % evs[0]["bid"], timeout=40)
        outs = []
        for x in r or []:
            outs += (x.get("payload") or {}).get("outcomes") or []
        print("3. страница матча: %.1f с, исходов %d, рынков %d" % (time.time() - t, len(outs), len(olimp_markets(outs, evs[0]["sk"]))))


def load_ls_har(path):
    """Дамп браузера -> (сырые матчи со списков, {id матча: ответ страницы матча})."""
    with open(path, encoding="utf-8") as fh:
        h = json.load(fh)
    evs, pages = {}, {}
    for e in h["log"]["entries"]:
        u = e["request"]["url"]
        t = e["response"]["content"].get("text") or ""
        if "lds-api.ligastavok.ru/rest/events/" not in u or e["request"]["method"] != "POST" or not t:
            continue
        try:
            r = json.loads(t).get("result")
        except ValueError:
            continue
        if u.endswith("/eventsList") and isinstance(r, dict):
            for x in r.get("data") or []:
                evs.setdefault(x["id"], x)
        elif u.endswith("/actionLine") and isinstance(r, dict) and r.get("markets"):
            pages[int(r["id"])] = r
            evs.setdefault(r["id"], r)
        elif u.endswith("/actionLines") and isinstance(r, list):
            for x in r:
                if x.get("markets"):
                    pages[int(x["id"])] = x
    return list(evs.values()), pages


def ls_set(args):
    """python arbphone.py --ls-set : спрашивает два заголовка из браузера и записывает их в config.json (на телефоне, никуда не отправляется)."""
    p = args.config or os.path.join(os.path.dirname(os.path.abspath(__file__)), "config.json")
    c = {}
    if os.path.exists(p):
        with open(p, encoding="utf-8") as fh:
            c = json.load(fh)
    print("Откройте в браузере ligastavok.ru (войдите в пустой аккаунт), F12 → Network → любой запрос к lds-api.ligastavok.ru → Request Headers.")
    cred = input("Значение x-api-cred: ").strip()
    user = input("Значение x-user: ").strip()
    if not cred or not user:
        print("Пустое значение — ничего не записано.")
        return
    h = dict(c.get("ls_headers") or {})
    h["x-api-cred"], h["x-user"] = cred, user
    c["ls_headers"] = h
    c["ligastavok"] = True
    with open(p, "w", encoding="utf-8") as fh:
        json.dump(c, fh, ensure_ascii=False, indent=2)
    print("Записано в %s. Проверка: python arbphone.py --ls-test" % p)


def ls_from_har(args):
    """python arbphone.py --ls-har ФАЙЛ.har : берёт x-api-cred и x-user из дампа браузера и записывает их в config.json (на телефоне)."""
    p = args.config or os.path.join(os.path.dirname(os.path.abspath(__file__)), "config.json")
    with open(args.ls_har, encoding="utf-8") as fh:
        h = json.load(fh)
    cred = user = ""
    for e in h["log"]["entries"]:
        if "lds-api.ligastavok.ru" not in e["request"]["url"]:
            continue
        hs = {x["name"].lower(): x["value"] for x in e["request"]["headers"]}
        if len(hs.get("x-api-cred", "")) > 50 and hs.get("x-user") and "REDACTED" not in hs["x-api-cred"]:
            cred, user = hs["x-api-cred"], hs["x-user"]
            break
    if not cred:
        print("В дампе нет заголовков x-api-cred / x-user (или они замазаны). Снимите дамп заново, не вырезая заголовки.")
        return
    c = {}
    if os.path.exists(p):
        with open(p, encoding="utf-8") as fh:
            c = json.load(fh)
    hh = dict(c.get("ls_headers") or {})
    hh["x-api-cred"], hh["x-user"] = cred, user
    c["ls_headers"] = hh
    c["ligastavok"] = True
    c["ls_token_saved"] = int(time.time())
    with open(p, "w", encoding="utf-8") as fh:
        json.dump(c, fh, ensure_ascii=False, indent=2)
    print("Записано в %s (x-api-cred %d знаков, x-user %d знаков). Проверка: python arbphone.py --ls-test" % (p, len(cred), len(user)))


def ls_test(cfg):
    """python arbphone.py --ls-test : проверка Лиги Ставок без токенов, с подробным выводом и несколькими вариантами заголовков."""
    variants = [("как есть", {}, []),
                ("без sec-* заголовков", {}, ["sec-fetch-dest", "sec-fetch-mode", "sec-fetch-site", "sec-ch-ua", "sec-ch-ua-mobile", "sec-ch-ua-platform"]),
                ("как мобильное приложение", {"x-application-name": "mobile"}, ["Origin", "Referer"]),
                ("как сайт (desktop)", {"x-application-name": "desktop"}, [])]
    ok = None
    for name, extra, drop in variants:
        c = dict(cfg, ls_headers=dict(cfg.get("ls_headers") or {}, **extra), ls_drop_headers=drop)
        try:
            r = _ls_post(c, "/rest/events/v2/filter", {"topEvents": False, "widgetVideo": False}, timeout=25)
            print("1. [%s] OK, видов спорта %d" % (name, len(r or [])))
            ok = c
            break
        except Exception as e:
            print("1. [%s] %s: %s" % (name, type(e).__name__, str(e)[:110]))
    if not ok:
        print("   Ни один вариант не прошёл. Проверьте: выключен ли VPN (сайт может не пускать с иностранных адресов),")
        print("   и открывается ли ligastavok.ru в браузере этого телефона. Если открывается — пришлите вывод этой команды.")
        return
    cfg = ok
    try:
        r = _ls_post(cfg, "/rest/events/v8/eventsList", {"gameId": [33], "limit": 5, "offset": 0, "topEvents": False, "view": "priority"}, timeout=25)
        a = [x["id"] for x in (r or {}).get("data") or []]
        r2 = _ls_post(cfg, "/rest/events/v8/eventsList", {"gameId": [33], "limit": 5, "exceptEventIds": a, "topEvents": False, "view": "priority"}, timeout=25)
        b = [x["id"] for x in (r2 or {}).get("data") or []]
        r3 = _ls_post(cfg, "/rest/events/v8/eventsList", {"gameId": [33], "limit": int(cfg["ls_limit"]), "topEvents": False, "view": "priority"}, timeout=40)
        print("2. футбол: всего %s, первая страница %d, следующая страница (exceptEventIds) другая: %s, страница на %d матчей: получено %d" % (
            (r or {}).get("total"), len(a), bool(b) and not set(a) & set(b), int(cfg["ls_limit"]), len((r3 or {}).get("data") or [])))
        if a:
            p = _ls_post(cfg, "/rest/events/v6/actionLine", {"id": a[0]}, timeout=25)
            print("3. страница матча %s: рынков %d, разобрано %d" % ((p.get("event") or {}).get("eventTitle"), len(p.get("markets") or {}), len(ls_markets(p, "football"))))
    except Exception as e:
        print("2/3. ОШИБКА %s: %s" % (type(e).__name__, e))


def betcity_test(cfg):
    """python arbphone.py --betcity-test : пошаговая проверка Бетсити с подробным выводом."""
    t0 = time.time()
    try:
        r = _bc_req(cfg, "/d/off/champs?rev=4&strip=dep_champs&ids_sp=1", timeout=20)
    except Exception as e:
        print("1. чемпионаты: ОШИБКА %s: %s" % (type(e).__name__, e))
        return
    ch = (r.get("sports") or {}).get("1") or {}
    chm = ch.get("chmps") or {}
    print("1. чемпионаты футбола: ответ получен за %.1f с, ключи ответа: %s, чемпионатов: %d" % (time.time() - t0, list(r.keys())[:6], len(chm)))
    if not chm:
        print("   сырой ответ (начало):", json.dumps(r, ensure_ascii=False)[:300])
        return
    h = str(cfg["betcity_hours"])
    ids = [str(c["id_ch"]) for c in chm.values() if not c.get("is_future") and not c.get("is_stat") and (c.get("cols") or {}).get(h, 0) > 0]
    print("   с матчами на %s ч: %d (пример: %s)" % (h, len(ids), ids[:3]))
    if not ids:
        c0 = next(iter(chm.values()))
        print("   пример чемпионата:", json.dumps({k: c0[k] for k in c0 if k in ("id_ch", "name_ch", "cols", "is_future", "is_stat")}, ensure_ascii=False)[:300])
        return
    for batch in (ids[:1], ids[:5]):
        t1 = time.time()
        try:
            r = _bc_req(cfg, "/d/off/events?rev=6&add=dep_events", "ids=" + ",".join(batch), timeout=40)
        except Exception as e:
            print("2. матчи пачкой из %d: ОШИБКА %s: %s" % (len(batch), type(e).__name__, e))
            continue
        n = sum(len(c.get("chmps") or {}) for c in (r.get("sports") or {}).values())
        ne = sum(len(c.get("evts") or {}) for s in (r.get("sports") or {}).values() for c in (s.get("chmps") or {}).values())
        print("2. матчи пачкой из %d чемпионатов: %.1f с, чемпионатов в ответе %d, событий %d" % (len(batch), time.time() - t1, n, ne))
        evs = bc_parse(r)
        print("   разобрано матчей (прематч): %d" % len(evs))
        for e in evs[:3]:
            print("   -", e["home"], "-", e["away"], time.strftime("%d.%m %H:%M", time.gmtime(e["start"] + 10800)), sorted(e["markets"])[:6])
        if ne and not evs:
            for s in (r.get("sports") or {}).values():
                for c in (s.get("chmps") or {}).values():
                    for eid, e in list((c.get("evts") or {}).items())[:2]:
                        print("   событие", eid, {k: e.get(k) for k in ("name_ht", "name_at", "date_ev", "is_online", "time_name", "dep_id_ev", "del_ev")}, "main" in e)
                    break
                break
    print("готово за %.0f с" % (time.time() - t0))


def load_bc_har(path):
    """Дамп браузера -> ответы events (с main) и ext."""
    with open(path, encoding="utf-8") as fh:
        h = json.load(fh)
    evs, exts = [], []
    for e in h["log"]["entries"]:
        u = e["request"]["url"]
        if "ad.betcity.ru/d/off/" not in u:
            continue
        c = e["response"]["content"]
        t = c.get("text") or ""
        if not t:
            continue
        if c.get("encoding") == "base64":
            t = base64.b64decode(t).decode("utf-8", "replace")
        try:
            r = json.loads(t).get("reply") or {}
        except ValueError:
            continue
        if "/off/ext?" in u:
            exts.append((u, r))
        elif "/off/events?" in u and (r.get("sports")):
            evs.append(r)
    return evs, exts


# ============================================================ сопоставление матчей

# ============================================================ БетБум (платформа Sporthub, protobuf по WebSocket)
# Формат разобран по HAR и сверен с экраном БетБума (Сан-Марино – Беларусь 20.0 / 7.8 / 1.13, Марсель – Ле-Ман 1.39 / 5.0 / 6.8).
#   запросы:  3{id,"all",8} x2; 4{id,01 02}; 6{id,{sub,1|2,2}} (2 = дерево турниров прематча);
#             8{id,{sub,2,<турнир>}} — матчи турнира; 16{id,{sub,<матч>}} — все рынки матча
#   ответы:   поле 7/9/17, внутри заголовок матча (id, sr:match, время UTC, команды) и исходы
#   исход:    ключ "sr:match:<id>/<рынок Sportradar>/<исход>?<параметры>", коэффициент — double в поле 10
#   рынки Sportradar: 1 = 1X2, 18 = тотал, 16 = фора (параметр hcp — линия хозяев), 10 = двойной шанс, 29 = обе забьют,
#                     60 / 68 / 66 = исход / тотал / фора 1-го тайма.  Угловых в разобранных матчах у БетБума не было.
BB_FOOT = 2
BB_KEY = re.compile(r"^sr:match:\d+/(\d+)/([^?]+)\?(.*)$")


def _pv(n):
    out = bytearray()
    while True:
        b, n = n & 0x7F, n >> 7
        if n:
            out.append(b | 0x80)
        else:
            out.append(b)
            return bytes(out)


def _pf(num, val):
    """Поле protobuf: int -> varint, str/bytes -> строка с длиной."""
    if isinstance(val, int):
        return _pv(num << 3) + _pv(val)
    if isinstance(val, str):
        val = val.encode()
    return _pv(num << 3 | 2) + _pv(len(val)) + val


def _pb_parse(b):
    i, out = 0, []
    while i < len(b):
        k, s = 0, 0
        while True:
            c = b[i]
            i += 1
            k |= (c & 0x7F) << s
            s += 7
            if not c & 0x80:
                break
        f, w = k >> 3, k & 7
        if f == 0:
            raise ValueError("field 0")
        if w == 0:
            v, s = 0, 0
            while True:
                c = b[i]
                i += 1
                v |= (c & 0x7F) << s
                s += 7
                if not c & 0x80:
                    break
        elif w == 2:
            ln, s = 0, 0
            while True:
                c = b[i]
                i += 1
                ln |= (c & 0x7F) << s
                s += 7
                if not c & 0x80:
                    break
            v = b[i:i + ln]
            i += ln
            if len(v) < ln:
                raise ValueError("trunc")
        elif w == 1:
            v = b[i:i + 8]
            i += 8
            if len(v) < 8:
                raise ValueError("trunc")
        elif w == 5:
            v = b[i:i + 4]
            i += 4
            if len(v) < 4:
                raise ValueError("trunc")
        else:
            raise ValueError("wire %d" % w)
        out.append((f, w, v))
    return out


def _pb_walk(b):
    """Обходит все вложенные сообщения: (словарь поле -> [(тип, значение)])."""
    try:
        fs = _pb_parse(b)
    except Exception:
        return
    if not fs:
        return
    d = {}
    for f, w, v in fs:
        d.setdefault(f, []).append((w, v))
    yield d
    for f, w, v in fs:
        if w == 2 and len(v) > 1:
            yield from _pb_walk(v)


def _pb_val(w, v):
    if w == 0:
        return v
    if w == 1:
        return struct.unpack("<d", v)[0]
    if w == 5:
        return struct.unpack("<f", v)[0]
    try:
        s = v.decode("utf8")
        return s if s.isprintable() else None
    except Exception:
        return None


def _bb_teams(raw):
    t = {}
    for f, w, v in _pb_parse(raw):
        if w == 2:
            for f2, w2, v2 in _pb_parse(v):
                if f2 == 3 and w2 == 2:
                    t[f] = v2.decode("utf8", "replace")
    return t.get(1), t.get(3)


def _bb_scan(b):
    """Одно сообщение -> (заголовки матчей {id: {...}}, исходы [(id матча, ключ, коэффициент)])."""
    heads, outs = {}, []
    for d in _pb_walk(b):
        k = d.get(1)
        if k and k[0][0] == 2 and 10 in d and 2 in d and 14 in d and d[10][0][0] == 1:
            key = _pb_val(*k[0])
            if isinstance(key, str) and key.startswith("sr:match:") and d[2][0][0] == 0:
                outs.append((d[2][0][1], key, _pb_val(*d[10][0])))
                continue
        s5 = d.get(5)
        if s5 and 13 in d and 16 in d and 1 in d and d[1][0][0] == 0:
            sr, tm = _pb_val(*s5[0]), _pb_val(*d[13][0])
            if isinstance(sr, str) and sr.startswith("sr:match:") and isinstance(tm, str):
                if 3 in d and d[3][0][1] != BB_FOOT:
                    continue
                try:
                    home, away = _bb_teams(d[16][0][1])
                    start = dt.datetime.strptime(tm[:19], "%Y-%m-%dT%H:%M:%S").replace(tzinfo=dt.timezone.utc).timestamp()
                except Exception:
                    continue
                if home and away:
                    heads[d[1][0][1]] = {"home": home, "away": away, "start": int(start),
                                         "tour": d[10][0][1] if 10 in d and d[10][0][0] == 0 else None}
    return heads, outs


def bb_markets(rows):
    """rows: [(ключ исхода, коэффициент)] одного матча -> рынки в общем формате (1X2, TOTAL, HCP, DC, BTTS, 1H:...)."""
    raw = collections.defaultdict(dict)
    for key, odds in rows:
        m = BB_KEY.match(key)
        if m and odds > 1.0:
            raw[(int(m.group(1)), m.group(3))][m.group(2)] = odds
    mk = {}
    for (mid, par), d in raw.items():
        pre = "1H:" if mid in (60, 66, 68) else ""
        try:
            if mid in (1, 60) and par == "" and {"1", "2", "3"} <= set(d):
                mk[pre + "1X2"] = {"1": d["1"], "X": d["2"], "2": d["3"]}
            elif mid in (18, 68) and par.startswith("total=") and "12" in d and "13" in d:
                L = float(par[6:])
                if (2 * L) % 1 == 0:
                    mk[pre + "TOTAL:%.2f" % L] = {"O": d["12"], "U": d["13"]}
            elif mid in (16, 66) and par.startswith("hcp=") and "1714" in d and "1715" in d:
                L = float(par[4:])
                if (2 * L) % 1 == 0:
                    mk[pre + "HCP:%.2f" % (L + 0.0)] = {"1": d["1714"], "2": d["1715"]}
            elif mid == 10 and par == "" and {"9", "10", "11"} <= set(d):
                mk["DC"] = {"1X": d["9"], "12": d["10"], "X2": d["11"]}
            elif mid == 29 and par == "" and "74" in d and "76" in d:
                mk["BTTS"] = {"Y": d["74"], "N": d["76"]}
        except ValueError:
            continue
    return mk


def bb_events(msgs, tour_names=None, now=None):
    """Сообщения БетБума -> список матчей в том же виде, что у Фонбета и Винлайна."""
    heads, rows = {}, collections.defaultdict(dict)
    for b in msgs:
        h, o = _bb_scan(b)
        heads.update(h)
        for eid, key, odds in o:
            rows[eid][key] = odds
    out = []
    for eid, h in heads.items():
        if now and h["start"] < now:
            continue
        mk = bb_markets(list(rows.get(eid, {}).items()))
        if mk:
            out.append({"bk": "betboom", "league": (tour_names or {}).get(h["tour"], ""), "home": h["home"],
                        "away": h["away"], "start": h["start"], "markets": mk, "id": eid})
    return out


def _bb_tours(b):
    out = {}
    for d in _pb_walk(b):
        if all(k in d for k in (1, 2, 3, 4, 6, 12)) and d[1][0][0] == 0 and d[2][0][0] == 0 and d[4][0][0] == 2:
            if d[2][0][1] == BB_FOOT:
                out[d[1][0][1]] = _pb_val(*d[4][0]) or ""
    return out


def _bb_tour_counts(b):
    """{id футбольного турнира: число матчей в нём (поле 9 дерева)} — чтобы крупные турниры запрашивать первыми."""
    out = {}
    for d in _pb_walk(b):
        if all(k in d for k in (1, 2, 3, 4, 6, 12)) and d[1][0][0] == 0 and d[2][0][0] == 0 and d[4][0][0] == 2:
            if d[2][0][1] == BB_FOOT:
                out[d[1][0][1]] = d[9][0][1] if 9 in d and d[9][0][0] == 0 else 0
    return out


def _rid():
    return "%06x" % random.getrandbits(24)


def _uuid7():
    ms = int(time.time() * 1000) & ((1 << 48) - 1)
    r = random.getrandbits(74)
    return str(uuid.UUID(int=(ms << 80) | (7 << 76) | ((r >> 62) << 64) | (2 << 62) | (r & ((1 << 62) - 1))))


def _bb_sub(b):
    """Id подзапроса, на который отвечает сообщение (None — не ответ)."""
    try:
        f0, w0, v0 = _pb_parse(b)[0]
        if f0 not in (7, 9, 17) or w0 != 2:
            return None
        for f, w, v in _pb_parse(v0):
            if f == 5 and w == 2:
                for f2, w2, v2 in _pb_parse(v):
                    if f2 == 4 and w2 == 2:
                        return v2.decode()
    except Exception:
        pass
    return None


def _bb_connect(cfg):
    try:
        import websocket
    except ImportError:
        sys.exit("Нужен пакет: pip install websocket-client")
    ws = websocket.create_connection(
        "%s?uuid=%s" % (cfg["betboom_ws"], cfg.get("betboom_uuid") or _uuid7()), timeout=10, origin="https://betboom.ru",
        subprotocols=["protobuf"],
        header=["User-Agent: " + BB_UA, "Accept-Language: ru,en;q=0.9", "Cache-Control: no-cache", "Pragma: no-cache"])
    try:
        ws.settimeout(3)
        ws.recv_data()                                           # приветствие сервера
    except Exception:
        pass
    for _ in range(2):
        ws.send_binary(_pf(3, _pf(1, _rid()) + _pf(2, "all") + _pf(3, 8)))
    return ws


def _bb_gather(ws, want, timeout, idle=5.0):
    import websocket
    got, seen = [], set()
    end = last = time.time()
    end += timeout
    ws.settimeout(1.0)
    t_ping = time.time()
    while time.time() < end and not want <= seen:
        if time.time() - t_ping >= 8:                              # браузер шлёт пинг каждые 10 с; без него сервер со временем замолкает
            t_ping = time.time()
            try:
                ws.send_binary(_pf(1, _pf(1, _rid())))
            except Exception:
                break
        try:
            op, data = ws.recv_data()
        except websocket.WebSocketTimeoutException:
            if time.time() - last > idle:
                break
            continue
        if op == websocket.ABNF.OPCODE_CLOSE:
            break
        if op == websocket.ABNF.OPCODE_BINARY:
            last = time.time()
            got.append(data)
            s = _bb_sub(data)
            if s:
                seen.add(s)
    return got, seen


def _bb_tours_chunk(ws, tids, cfg):
    """Подписка на группу турниров по одному соединению -> (сообщения, получено ответов, запрошено)."""
    subs, n, by_sub = set(), max(1, int(cfg["betboom_batch"])), {}
    for i in range(0, len(tids), n):
        body = b""
        for tid in tids[i:i + n]:
            sub = _rid()
            subs.add(sub)
            by_sub[sub] = tid
            body += _pf(2, _pf(1, sub) + _pf(2, 2) + _pf(3, tid))
        ws.send_binary(_pf(8, _pf(1, _rid()) + body))
        time.sleep(0.05)
    msgs, seen = _bb_gather(ws, subs, cfg["betboom_timeout"])
    return msgs, len(seen & subs), len(subs), [t for sb, t in by_sub.items() if sb not in seen]


def betboom_fetch(cfg):
    """Дерево турниров, затем матчи всех футбольных турниров прематча. Возвращает (сообщения, {id турнира: название})."""
    ws = _bb_connect(cfg)
    try:
        ws.send_binary(_pf(4, _pf(1, _rid()) + _pf(2, b"\x01\x02")))
        sub_live, sub_tree = _rid(), _rid()
        for kind, sub in ((1, sub_live), (2, sub_tree)):
            ws.send_binary(_pf(6, _pf(1, _rid()) + _pf(2, _pf(1, sub) + _pf(2, kind) + _pf(3, 2))))
        got, _ = _bb_gather(ws, {sub_tree}, 25)
        tree = next((m for m in got if _bb_sub(m) == sub_tree), None)
        if tree is None:
            raise RuntimeError("БетБум: дерево турниров не пришло")
        names = {t: n for t, n in _bb_tours(tree).items() if not FAKE_LEAGUE.search(n)}
        cnt = _bb_tour_counts(tree)
        tids = sorted(names, key=lambda t: (-cnt.get(t, 0), t))      # крупные турниры — первыми
        k = int(cfg.get("betboom_chunk") or 0)
        chunks = [tids[i:i + k] for i in range(0, len(tids), k)] if k > 0 else [tids]
        msgs, seen_n, subs_n, miss = _bb_tours_chunk(ws, chunks[0], cfg)
        if len(chunks) > 1:                                    # остальные турниры — отдельными соединениями, параллельно
            res = {}

            def work(ix):
                try:
                    w2 = _bb_connect(cfg)
                    try:
                        w2.send_binary(_pf(4, _pf(1, _rid()) + _pf(2, b"\x01\x02")))
                        res[ix] = _bb_tours_chunk(w2, chunks[ix], cfg)
                    finally:
                        w2.close()
                except Exception as e:
                    res[ix] = ([], 0, len(chunks[ix]), list(chunks[ix]), type(e).__name__)
            todo = list(range(1, len(chunks)))
            for j in range(0, len(todo), 4):                   # не больше 4 соединений одновременно
                th = [threading.Thread(target=work, args=(ix,), daemon=True) for ix in todo[j:j + 4]]
                for t in th:
                    t.start()
                for t in th:
                    t.join(cfg["betboom_timeout"] + 15)
            fails = collections.Counter(r[4] for r in res.values() if len(r) > 4)
            for r in res.values():
                msgs += r[0]
                seen_n += r[1]
                subs_n += r[2]
                miss += r[3]
            if fails:
                log("БетБум: часть соединений не удалась: %s" % dict(fails))
        for rnd in range(int(cfg.get("betboom_retry_rounds", 3))):      # турниры без ответа — ещё раз, новыми соединениями
            if not miss or not k:
                break
            left, miss = miss, []
            parts = [left[i:i + k] for i in range(0, len(left), k)]
            res2 = {}

            def work2(ix):
                try:
                    w2 = _bb_connect(cfg)
                    try:
                        w2.send_binary(_pf(4, _pf(1, _rid()) + _pf(2, b"\x01\x02")))
                        res2[ix] = _bb_tours_chunk(w2, parts[ix], cfg)
                    finally:
                        w2.close()
                except Exception:
                    res2[ix] = ([], 0, 0, list(parts[ix]))
            for j in range(0, len(parts), 4):
                th = [threading.Thread(target=work2, args=(ix,), daemon=True) for ix in range(j, min(j + 4, len(parts)))]
                for t in th:
                    t.start()
                for t in th:
                    t.join(cfg["betboom_timeout"] + 15)
            for r in res2.values():
                msgs += r[0]
                seen_n += r[1]
                miss += r[3]
        log("БетБум: турниров %d, ответов %d из %d, без ответа после повторов %d (соединений %d)" % (len(tids), seen_n, subs_n, len(miss), len(chunks)))
        return msgs, names
    finally:
        try:
            ws.close()
        except Exception:
            pass


def bb_dump(cfg):
    """Диагностика БетБума для добавления киберспорта: какие виды спорта есть в дереве + сырые данные нескольких киберспортивных турниров.
    Пишет ~/bb_dump.json (и копию в Загрузки) — файл можно отправить разработчику. Ничего никуда не отправляет."""
    import base64
    ws = _bb_connect(cfg)
    out = {"sports": {}, "tours": [], "raw": []}
    try:
        ws.send_binary(_pf(4, _pf(1, _rid()) + _pf(2, b"\x01\x02")))
        sub_live, sub_tree = _rid(), _rid()
        for kind, sub in ((1, sub_live), (2, sub_tree)):
            ws.send_binary(_pf(6, _pf(1, _rid()) + _pf(2, _pf(1, sub) + _pf(2, kind) + _pf(3, 2))))
        got, _ = _bb_gather(ws, {sub_tree}, 25)
        tree = next((m for m in got if _bb_sub(m) == sub_tree), None)
        if tree is None:
            print("дерево не пришло")
            return
        tours = []
        for d in _pb_walk(tree):
            if all(k in d for k in (1, 2, 3, 4, 6, 12)) and d[1][0][0] == 0 and d[2][0][0] == 0 and d[4][0][0] == 2:
                tours.append((d[2][0][1], d[1][0][1], _pb_val(*d[4][0]) or "", d[9][0][1] if 9 in d and d[9][0][0] == 0 else 0))
        by = collections.defaultdict(list)
        for sp, tid, nm, cnt in tours:
            by[sp].append((tid, nm, cnt))
        for sp, lst in sorted(by.items()):
            out["sports"][str(sp)] = {"tournaments": len(lst), "matches": sum(c for _, _, c in lst), "sample": [n for _, n, _ in lst[:6]]}
            print("вид спорта %s: турниров %d, матчей %d, например: %s" % (sp, len(lst), sum(c for _, _, c in lst), "; ".join(n for _, n, _ in lst[:3])))
        esp = re.compile(r"cs2|counter|dota|valorant|league of|lol|blast|pgl|esl|cct|iem|overwatch|rainbow|киберспорт", re.I)
        cand = [(sp, tid, nm, cnt) for sp, tid, nm, cnt in tours if sp != BB_FOOT and esp.search(nm) and cnt > 0]
        cand.sort(key=lambda x: -x[3])
        pick = cand[:3]
        out["tours"] = [{"sport": sp, "id": tid, "name": nm, "matches": cnt} for sp, tid, nm, cnt in pick]
        print("киберспортивных турниров для выгрузки:", len(pick))
        if pick:
            msgs, n, subs_n, miss = _bb_tours_chunk(ws, [t[1] for t in pick], cfg)
            out["raw"] = [base64.b64encode(zlib.compress(m, 9)).decode() for m in msgs]
            print("получено сообщений:", len(msgs))
    finally:
        try:
            ws.close()
        except Exception:
            pass
    path = os.path.expanduser("~/bb_dump.json")
    with open(path, "w", encoding="utf-8") as fh:
        json.dump(out, fh, ensure_ascii=False)
    print("файл:", path, os.path.getsize(path) // 1024, "КБ")
    for d in ("/sdcard/Download", "/storage/emulated/0/Download"):
        if os.path.isdir(d):
            try:
                shutil.copy(path, os.path.join(d, "bb_dump.json"))
                print("скопировано в", d + "/bb_dump.json")
                break
            except Exception as e:
                print("не удалось скопировать:", e)


def _bb_outer_sub(b):
    """Id подзапроса из верхнего уровня ответа (у страниц матчей он здесь, а не внутри)."""
    try:
        top = _pb_parse(b)
        for f, w, v in _pb_parse(top[0][2]):
            if f == 4 and w == 2:
                return v.decode()
    except Exception:
        pass
    return None


def betboom_details(cfg, eids, timeout=75):
    """Страницы матчей БетБума по одной, как в браузере: открыли (поле 16) -> получили ответ -> отписались (поле 18).
    Одновременно сервер держит лишь несколько страниц, поэтому пачкой приходило 3 из 20."""
    import websocket
    ws = _bb_connect(cfg)
    got, end = [], time.time() + timeout
    try:
        ws.settimeout(1.0)
        for eid in eids:
            if time.time() > end:
                break
            sub = _rid()
            ws.send_binary(_pf(16, _pf(1, _rid()) + _pf(2, _pf(1, sub) + _pf(2, eid))))
            t_end, last, done = min(end, time.time() + 10), time.time(), False
            try:
                ws.send_binary(_pf(1, _pf(1, _rid())))
            except Exception:
                pass
            while time.time() < t_end and not done:
                try:
                    op, data = ws.recv_data()
                except websocket.WebSocketTimeoutException:
                    if time.time() - last > 4.0:
                        break
                    continue
                if op == websocket.ABNF.OPCODE_CLOSE:
                    raise ConnectionError("БетБум закрыл соединение")
                if op == websocket.ABNF.OPCODE_BINARY:
                    last = time.time()
                    got.append(data)
                    if _bb_outer_sub(data) == sub or _bb_sub(data) == sub:
                        done = True
            ws.send_binary(_pf(18, _pf(1, _rid()) + _pf(2, _pf(1, sub) + _pf(2, eid))))
        return got
    finally:
        try:
            ws.close()
        except Exception:
            pass


BB_NUM = re.compile(r"\(\s*([-+]?\d+(?:\.\d+)?)\s*\)")
BB_PAGE_SCOPE = {"Основное время": "", "1-й тайм": "1H:", "Угловые": "CRN:"}


def _bb_f(raw):
    out = {}
    for f, w, v in _pb_parse(raw):
        out.setdefault(f, []).append((w, v))
    return out


def bb_page_markets(b):
    """Страница матча БетБума (ответ на запрос поля 16) -> {id матча: рынки}. Рынки: исход, ДШ, обе забьют, тоталы, форы
    за матч, 1-й тайм и угловые (тип рынка = поле 13, область = поле 20: «Основное время» / «1-й тайм» / «Угловые»)."""
    try:
        top = _pb_parse(b)
        box = [v for f, w, v in _pb_parse(top[0][2]) if f == 5 and w == 2][0]
        items = [v for f, w, v in _pb_parse(box) if f == 8 and w == 2][0]
        items = _pb_parse(items)
    except Exception:
        return {}
    teams, rows = {}, collections.defaultdict(list)
    for f, w, v in items:
        if w != 2:
            continue
        try:
            o = _bb_f(v)
            if f == 1 and 16 in o and 1 in o:
                teams[o[1][0][1]] = _bb_teams(o[16][0][1])
            elif f == 2 and 13 in o and 10 in o and 2 in o and 20 in o and o[10][0][0] == 1:
                rows[o[2][0][1]].append((o[13][0][1], o[20][0][1].decode("utf8", "replace"),
                                         o[5][0][1].decode("utf8", "replace") if 5 in o else "",
                                         struct.unpack("<d", o[10][0][1])[0]))
        except Exception:
            continue
    res = {}
    for mid, rs in rows.items():
        home, away = teams.get(mid, (None, None))
        raw = collections.defaultdict(dict)
        for t, scope, name, odds in rs:
            if odds <= 1.0:
                continue
            if t in (120, 127, 131, 132) and scope == "Угловые":
                pre = "1H:CRN:"                                        # «1-й тайм: …» по угловым
                t = {120: 20, 127: 3, 131: 2, 132: 1}[t]
            elif t in (1, 2, 3, 20, 14) and scope in BB_PAGE_SCOPE:
                pre = BB_PAGE_SCOPE[scope]
                if t in (20, 14) and pre != "":
                    continue                                          # ДШ и «обе забьют» — только за матч
            else:
                continue
            m = BB_NUM.search(name)
            if t == 1 and name in ("П1", "X", "Х", "П2"):
                raw[(pre, "1X2")][{"П1": "1", "X": "X", "Х": "X", "П2": "2"}[name]] = odds
            elif t == 20 and name in ("1X", "12", "X2"):
                raw[(pre, "DC")][name] = odds
            elif t == 14 and name in ("Да", "Нет"):
                raw[(pre, "BTTS")]["Y" if name == "Да" else "N"] = odds
            elif t == 3 and m and (name.startswith("Больше") or name.startswith("Меньше")):
                L = abs(float(m.group(1)))
                raw[(pre, "TOTAL:%.2f" % L)]["O" if name.startswith("Больше") else "U"] = odds
            elif t == 2 and m and home and away:
                v = float(m.group(1))
                if name.startswith(home):
                    raw[(pre, "HCP:%.2f" % (v + 0.0))]["1"] = odds
                elif name.startswith(away):
                    raw[(pre, "HCP:%.2f" % (-v + 0.0))]["2"] = odds
        mk = {}
        for (pre, k), d in raw.items():
            need = {"1X2": {"1", "X", "2"}, "DC": {"1X", "12", "X2"}, "BTTS": {"Y", "N"}}.get(k.split(":")[0],
                                                                                            {"O", "U"} if k.startswith("TOTAL") else {"1", "2"})
            if need <= set(d):
                if pre == "CRN:" and k in ("DC", "BTTS"):
                    continue
                mk[pre + k] = d
        if mk:
            res[mid] = mk
    return res


def add_bb_details(cfg, pairs):
    """Для ближайших совпавших матчей запрашиваем страницу БетБума и дополняем рынки."""
    cand = sorted(pairs, key=lambda p: p[0]["start"])[:cfg["betboom_detail_max"]]
    if not cand:
        return
    try:
        msgs = betboom_details(cfg, [p[0]["id"] for p in cand])
    except SystemExit:
        raise
    except Exception as e:
        log("страницы матчей БетБума недоступны: %s: %s" % (type(e).__name__, e))
        return
    rows = collections.defaultdict(dict)                       # коэффициенты берём по id матча, заголовок на странице не нужен
    for b in msgs:
        for eid, key, odds in _bb_scan(b)[1]:
            rows[eid][key] = odds
    pages = {}
    for b in msgs:
        pages.update(bb_page_markets(b))
    n = 0
    log("БетБум страницы: сообщений %d, матчей с коэффициентами %d, страниц разобрано %d" % (len(msgs), len(rows), len(pages)))
    for w, f, sw in cand:
        mk = bb_markets(list(rows.get(w["id"], {}).items()))
        mk.update(pages.get(w["id"], {}))
        if mk:
            w["markets"].update(mk)
            n += 1
    log("БетБум: страниц матчей запрошено %d, получено %d" % (len(cand), n))


def load_bb_har(paths):
    """Офлайн: сообщения WebSocket БетБума из одного или нескольких HAR."""
    msgs = []
    for p in paths:
        with open(p, encoding="utf-8") as fh:
            for e in json.load(fh)["log"]["entries"]:
                if "tree_ws" in e["request"]["url"]:
                    msgs += [base64.b64decode(m["data"]) for m in e.get("_webSocketMessages", [])
                             if m["type"] == "receive" and m["opcode"] == 2]
    return msgs


# ============================================================ Polymarket (открытый API без входа, цены = вероятности)

PM_CACHE = {"t": 0.0, "ev": [], "pause": 0.0, "tags": {}}
PM_TAGS = {"soccer": "football", "epl": "football", "ucl": "football", "laliga": "football", "bundesliga": "football",
           "serie-a": "football", "ligue-1": "football", "nba": "basketball", "nhl": "hockey", "atp": "tennis", "wta": "tennis"}
PM_HDR = {"User-Agent": "Mozilla/5.0 (Linux; Android 14) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/130.0 Mobile Safari/537.36",
          "Accept": "application/json"}
_PM_TR = dict(zip("абвгдеёжзийклмнопрстуфхцчшщъыьэюя",
                  ["a", "b", "v", "g", "d", "e", "e", "zh", "z", "i", "i", "k", "l", "m", "n", "o", "p", "r", "s", "t", "u", "f", "h",
                   "ts", "ch", "sh", "sh", "", "i", "", "e", "iu", "ia"]))


PM_ALIAS = {"bayern": "бавария", "paris saint": "псж", "paris sg": "псж", "inter milan": "интер", "internazionale": "интер",
            "olympique de marseille": "марсель", "olympique marseille": "марсель", "olympique lyon": "лион", "sporting cp": "спортинг",
            "wolverhampton": "вулверхэмптон", "nottingham forest": "ноттингем форест", "bayer leverkusen": "байер леверкузен",
            "rb leipzig": "рб лейпциг", "napoli": "наполи", "ac milan": "милан", "as roma": "рома", "psv": "псв", "benfica": "бенфика"}


def pm_skel(s):
    """Название (русское или английское) -> «скелет» для сравнения: латиница без служебных слов, гласные и двойные буквы убраны."""
    s = (s or "").lower().replace("ё", "е")
    for k, v in PM_ALIAS.items():
        if k in s:
            s = v
            break
    s = "".join(_PM_TR.get(c, c) for c in s)
    s = re.sub(r"\b(fc|cf|afc|sc|ac|as|fk|club|de|the|city of|real|ii|u\d\d)\b", " ", s)
    s = re.sub(r"[^a-z0-9 ]", " ", s)
    s = s.replace("ph", "f").replace("ck", "k").replace("qu", "kv").replace("x", "ks").replace("w", "v").replace("j", "i").replace("y", "i")
    s = s.replace("c", "k").replace("q", "k").replace("h", "")
    s = re.sub(r"[aeiou]", "", s)
    s = re.sub(r"(.)\1+", r"\1", s)
    return re.sub(r"\s+", "", s)


def pm_sim(a, b):
    x, y = pm_skel(a), pm_skel(b)
    if not x or not y:
        return 0.0
    r = difflib.SequenceMatcher(None, x, y).ratio()
    if len(x) >= 4 and len(y) >= 4 and (x in y or y in x):
        r = max(r, 0.85)
    return r


PM_HDR2 = {"User-Agent": PM_HDR["User-Agent"], "Accept": "*/*", "Accept-Language": "ru-RU,ru;q=0.9,en;q=0.8",
           "Origin": "https://polymarket.com", "Referer": "https://polymarket.com/"}


def _pm_get(cfg, path, timeout=30):
    """GET к gamma-API с заголовками браузера (без них Cloudflare отвечает 406). Сначала curl, затем встроенный Python."""
    url = cfg.get("polymarket_url", "https://gamma-api.polymarket.com") + path
    errs = []
    if cfg.get("polymarket_curl", True) and shutil.which("curl"):
        cmd = ["curl", "-s", "-S", "--compressed", "--max-time", str(timeout), "-w", "\n%{http_code}"]
        for k, v in PM_HDR2.items():
            cmd += ["-H", "%s: %s" % (k, v)]
        r = subprocess.run(cmd + [url], capture_output=True, timeout=timeout + 10)
        body, _, code = r.stdout.rpartition(b"\n")
        if code.strip() == b"200":
            return json.loads(body)
        errs.append("curl HTTP %s %s" % (code.strip().decode("ascii", "ignore"), body[:120].decode("utf-8", "ignore").replace("\n", " ")))
    try:
        return json.loads(http_get(url, dict(PM_HDR2, **{"Accept-Encoding": "gzip"}), timeout))
    except urllib.error.HTTPError as e:
        errs.append("python HTTP %s" % e.code)
    raise RuntimeError("; ".join(errs) + " [" + path[:60] + "]")


def _pm_f(x):
    try:
        return float(x)
    except (TypeError, ValueError):
        return None


def _pm_lst(x):
    if isinstance(x, str):
        try:
            x = json.loads(x)
        except ValueError:
            return []
    return x if isinstance(x, list) else []


def _pm_buy(m, idx, fee):
    """Цена покупки исхода idx (Yes=0, No=1) -> коэффициент с учётом комиссии биржи. None — рынок без цены."""
    ask, bid = _pm_f(m.get("bestAsk")), _pm_f(m.get("bestBid"))
    pr = _pm_lst(m.get("outcomePrices"))
    if idx == 0:
        p = ask if ask else (_pm_f(pr[0]) if pr else None)
    else:
        p = (1.0 - bid) if bid else (_pm_f(pr[1]) if len(pr) > 1 else None)
    if not p or not 0.02 <= p <= 0.98:
        return None
    return round(1.0 / (p + fee * p * (1.0 - p)), 3)


def pm_markets(ev, sk, home, away, fee_on=True):
    mk, ml = {}, {}
    for m in ev.get("markets") or []:
        if m.get("closed") or m.get("active") is False or m.get("acceptingOrders") is False:
            continue
        t = m.get("sportsMarketType") or ""
        fs = m.get("feeSchedule") or {}
        fee = (_pm_f(fs.get("rate")) or 0.0) if (fee_on and m.get("feesEnabled")) else 0.0
        outs = _pm_lst(m.get("outcomes"))
        title = (m.get("groupItemTitle") or "").strip()
        if t == "moneyline":
            c = _pm_buy(m, 0, fee)
            if not c:
                continue
            if re.match(r"(draw|ничья)", title, re.I):
                ml["X"] = c
            elif pm_sim(title, home) >= pm_sim(title, away):
                ml["1"] = c
            else:
                ml["2"] = c
        elif t == "totals":
            line = _pm_f(m.get("line"))
            if line is None or (line * 2) != int(line * 2) or len(outs) != 2:
                continue
            o, u = ((_pm_buy(m, 0, fee), _pm_buy(m, 1, fee)) if str(outs[0]).lower().startswith(("over", "бол")) else (_pm_buy(m, 1, fee), _pm_buy(m, 0, fee)))
            if o and u:
                mk["TOTAL:%.2f" % line] = {"O": o, "U": u}
        elif t == "both_teams_to_score" and len(outs) == 2:
            y, n = _pm_buy(m, 0, fee), _pm_buy(m, 1, fee)
            if y and n and str(outs[0]).lower().startswith(("yes", "да")):
                mk["BTTS"] = {"Y": y, "N": n}
    if sk == "football":
        if len(ml) == 3:
            mk["1X2"] = {"1": ml["1"], "X": ml["X"], "2": ml["2"]}
    elif "1" in ml and "2" in ml and "X" not in ml:
        mk["ML"] = {"1": ml["1"], "2": ml["2"]}
    return mk


def pm_parse(events, sk, now=None):
    now = now or time.time()
    out = []
    for e in events or []:
        if e.get("closed") or e.get("live") or e.get("ended"):
            continue
        gs = e.get("gameStartTime") or e.get("startTime")
        if not gs:
            continue
        try:
            start = int(dt.datetime.fromisoformat(str(gs).replace("Z", "+00:00").replace(" ", "T")).timestamp())
        except ValueError:
            continue
        if start < now:
            continue
        teams = [t.get("name") for t in (e.get("teams") or []) if t.get("name")]
        if len(teams) != 2:
            m = re.match(r"(.+?)\s+(?:vs\.?|v)\s+(.+)", e.get("title") or "")
            if not m:
                continue
            teams = [m.group(1).strip(), m.group(2).strip()]
        if FAKE_LEAGUE.search(e.get("title") or ""):
            continue
        mk = pm_markets(e, sk, teams[0], teams[1])
        if mk:
            out.append({"bk": "polymarket", "home": teams[0], "away": teams[1], "start": start, "league": e.get("seriesSlug") or "",
                        "markets": mk, "bid": str(e.get("id") or e.get("slug")), "sk": sk, "pm": True})
    return out


def polymarket_fetch(cfg):
    """Матчи Polymarket по тегам спорта: GET /events?tag_slug=...&closed=false -> список событий (разобранных)."""
    now = time.time()
    if now < PM_CACHE["pause"]:
        return PM_CACHE["ev"]
    if PM_CACHE["ev"] and now - PM_CACHE["t"] < cfg.get("polymarket_ttl", 120):
        return PM_CACHE["ev"]
    out, seen = [], set()
    lim = now + (cfg.get("horizon_hours") or 72) * 3600 + 6 * 3600
    ok_any = False
    for slug in cfg.get("polymarket_tags", list(PM_TAGS)):
        sk = PM_TAGS.get(slug, "football")
        try:
            for off in range(0, 600, 100):
                q = "/events?tag_slug=%s&closed=false&active=true&limit=100&offset=%d&order=startDate&ascending=true&start_date_min=%s" % (slug, off, time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(now - 86400)))
                evs = _pm_get(cfg, q)
                if isinstance(evs, dict):
                    evs = evs.get("events") or evs.get("data") or []
                if not isinstance(evs, list):
                    break
                ok_any = True
                for e in evs:
                    if e.get("id") in seen:
                        continue
                    seen.add(e.get("id"))
                    out.extend(x for x in pm_parse([e], sk, now) if x["start"] <= lim)
                if len(evs) < 100:
                    break
        except Exception as e:
            log("Polymarket (%s): %s: %s" % (slug, type(e).__name__, e))
            if not ok_any:
                PM_CACHE["pause"] = now + 300
                log("Polymarket недоступен с этого подключения (следующая попытка через 5 минут)")
                return PM_CACHE["ev"]
    PM_CACHE["ev"], PM_CACHE["t"] = out, now
    log("Polymarket: матчей %d" % len(out))
    return out


def match_events_pm(pm, fon):
    """Названия у Polymarket английские, у остальных БК русские: сравниваем «скелеты» (транслит без гласных), время старта ±5 мин."""
    idx = collections.defaultdict(list)
    for f in fon:
        idx[f["start"] // 60].append(f)
    used, pairs = set(), []
    for w in pm:
        m0, best = w["start"] // 60, None
        for d in range(-5, 6):
            for f in idx.get(m0 + d, []):
                if f["id"] in used or f.get("sk", "football") != w["sk"]:
                    continue
                if w["sk"] == "football" and _flags(f["home"]) != _flags(f["away"]) and False:
                    continue
                for swapped in (False, True):
                    h2, a2 = (f["away"], f["home"]) if swapped else (f["home"], f["away"])
                    s1, s2 = pm_sim(w["home"], h2), pm_sim(w["away"], a2)
                    sc = min(s1, s2)
                    if sc >= 0.55 and (s1 + s2) / 2 >= 0.68 and (best is None or sc > best[0]):
                        best = (sc, f, swapped)
        if best:
            used.add(best[1]["id"])
            pairs.append((w, best[1], best[2]))
    return pairs


def polymarket_test(cfg):
    print("Polymarket: проверка (только чтение, без входа)")
    try:
        t0 = time.time()
        evs = polymarket_fetch(dict(cfg, polymarket_tags=cfg.get("polymarket_tags", list(PM_TAGS))))
        print("матчей получено: %d за %.1f с" % (len(evs), time.time() - t0))
        for e in evs[:8]:
            print(" ", time.strftime("%d.%m %H:%M", time.localtime(e["start"])), e["home"], "-", e["away"], {k: v for k, v in list(e["markets"].items())[:3]})
    except Exception as e:
        print("ошибка:", type(e).__name__, e)



# ============================================================ 1win (top-parser: список матчей по HTTP + коэффициенты по socket.io)

OW_API = "https://api-gateway.top-parser.com"
OW_WS = "wss://api-gateway.top-parser.com/push-server-v2/"
OW_PID = "44ba10e5-7df2-47ab-a44d-dc93803c7a6e"
OW_SPORTS = {18: "football", 35: "hockey", 23: "basketball", 33: "tennis", 27: "volleyball", 24: "table-tennis", 34: "handball",
             28: "futsal", 21: "am-football", 29: "baseball", 142: "esports", 47: "esports", 99: "esports"}
OW_CACHE = {"t": 0.0, "ev": [], "pause": 0.0, "fails": 0}
OW_HDR = {"User-Agent": PM_HDR["User-Agent"], "Accept": "application/json", "Content-Type": "application/json",
          "Accept-Language": "ru,en;q=0.9", "Origin": "https://one-vv8027.com", "Referer": "https://one-vv8027.com/",
          "x-external-partner-id": OW_PID, "x-lang": "ru-RU"}
_OW_3W = ("Результат основного времени", "Результат матча (основное время)", "Результат")
_OW_ML_OT = ("Победитель (включая ОТ)", "Победитель (вкл. ОТ)", "Победа в матче (включая доп. иннинги)")
_OW_HCP_OT = ("Фора (включая ОТ)", "Фора (вкл. ОТ)", "Фора (включая доп. иннинги)")
_OW_TOT_OT = ("Тотал (включая ОТ)", "Тотал (вкл. ОТ)", "Тотал (включая доп. иннинги)")


def _ow_post(cfg, path, body, timeout=30):
    url = cfg.get("onewin_api", OW_API) + path
    data = json.dumps(body)
    errs = []
    if cfg.get("onewin_curl", True) and shutil.which("curl"):
        cmd = ["curl", "-s", "-S", "--compressed", "--max-time", str(timeout), "-w", "\n%{http_code}", "-X", "POST", "--data", data]
        for k, v in OW_HDR.items():
            cmd += ["-H", "%s: %s" % (k, v)]
        r = subprocess.run(cmd + [url], capture_output=True, timeout=timeout + 10)
        b, _, code = r.stdout.rpartition(b"\n")
        if code.strip() == b"200":
            return json.loads(b)
        errs.append("curl HTTP %s %s" % (code.strip().decode("ascii", "ignore"), b[:100].decode("utf-8", "ignore").replace("\n", " ")))
    try:
        req = urllib.request.Request(url, data=data.encode(), headers=OW_HDR)
        with urllib.request.urlopen(req, timeout=timeout) as r:
            return json.loads(r.read().decode("utf-8", "replace"))
    except Exception as e:
        errs.append("python %s" % type(e).__name__)
    raise RuntimeError("; ".join(errs) + " [" + path + "]")


def ow_list(cfg, sport_id, now):
    """Список матчей вида спорта (до onewin_per_sport штук, постранично, если сервер отдаёт страницы)."""
    out, seen = [], set()
    per = int(cfg.get("onewin_per_sport", 300))
    step = 100
    for off in range(0, per, step):
        body = {"service": "prematch", "sportId": sport_id, "excludeSportType": "polybet", "limit": step}
        if off:
            body["offset"] = off
        j = _ow_post(cfg, "/matches/get-many", body)
        items = ((j.get("result") or {}).get("items")) or []
        new = [x for x in items if x.get("id") not in seen]
        for x in new:
            seen.add(x.get("id"))
        out += new
        if len(items) < step or not new:
            break
    return out


def ow_events(items, now=None, until=None):
    """Ответ списка -> [{bk, home, away, start, league, markets:{}, bid, sk}] (рынки добавляются позже из сокета)."""
    now = now or time.time()
    out = []
    for x in items:
        sk = OW_SPORTS.get(x.get("sportId"))
        h, a = (x.get("homeTeam") or {}).get("name"), (x.get("awayTeam") or {}).get("name")
        start = int(x.get("startAt") or 0)
        if not sk or not h or not a or x.get("serviceV2") not in (None, "prematch") or start < now or (until and start > until):
            continue
        if (x.get("homeTeam") or {}).get("slug", "").endswith("outrights") or (x.get("awayTeam") or {}).get("slug") == "outrights":
            continue
        slug = ((x.get("tournament") or {}).get("slug") or "").replace("-", " ")
        if FAKE_LEAGUE.search(slug) and sk != "esports":
            continue
        out.append({"bk": "onewin", "home": h.strip(), "away": a.strip(), "start": start, "league": slug, "markets": {}, "bid": int(x["id"]), "sk": sk,
                    "tid": x.get("tournamentId")})
    return out


def ow_markets(groups, sk, home, away):
    """oddsGroups матча 1win -> рынки в нашем виде (основное время; фора/тотал — только целые и половинные линии)."""
    mk = {}
    byname = {}
    for g in groups or []:
        byname.setdefault((g.get("name") or "").strip(), g)

    def odds(g):
        out = []
        for o in g.get("oddsList") or []:
            try:
                c = float(o.get("cf"))
            except (TypeError, ValueError):
                continue
            if c > 1.0 and o.get("status", 1) == 1:
                v = (o.get("vars") or {}).get("v1")
                out.append((o.get("outcome"), v, c, o.get("name") or ""))
        return out

    def pick(names):
        for n in names:
            if n in byname:
                return byname[n]
        return None

    def hcp(g, pre=""):
        d = {}
        for oc, v, c, _ in odds(g):
            h = _ol_line(v)
            if h is None or oc not in ("1", "2"):
                continue
            line = h if oc == "1" else -h
            if abs(line) >= _OL_MIN_HCP.get(sk, 0):
                d.setdefault(line, {})[oc] = c
        for line, dd in d.items():
            if len(dd) == 2:
                mk["%sHCP:%.2f" % (pre, line + 0.0)] = dd

    def tot(g, pre="", minv=None):
        d = {}
        for oc, v, c, _ in odds(g):
            t = _ol_line(v)
            if t is None or oc not in ("over", "under") or t < (_OL_MIN_TOTAL.get(sk, 0) if minv is None else minv):
                continue
            d.setdefault(t, {})["O" if oc == "over" else "U"] = c
        for t, dd in d.items():
            if len(dd) == 2:
                mk["%sTOTAL:%.2f" % (pre, t)] = dd

    if sk == "esports":
        g = byname.get("Победитель")
        if g:
            d = {oc: c for oc, _, c, _ in odds(g) if oc in ("1", "2")}
            if len(d) == 2:
                mk["ML"] = d
        g = byname.get("Фора по картам")
        if g:
            hcp(g)
        g = byname.get("Тотал карт")
        if g:
            tot(g, minv=0)
        return mk
    g = pick(_OW_3W) if sk in ("football", "hockey", "handball", "futsal") else None
    if g:
        d = {{"1": "1", "x": "X", "2": "2"}[oc]: c for oc, _, c, _ in odds(g) if oc in ("1", "x", "2")}
        if len(d) == 3:
            mk["1X2"] = d
    if sk != "football":
        g = pick(_OW_ML_OT) or byname.get("Победитель")
        if g:
            d = {oc: c for oc, _, c, _ in odds(g) if oc in ("1", "2")}
            if len(d) == 2:
                mk["ML"] = d
    g = byname.get("Двойной шанс")
    if g and sk in ("football", "hockey", "handball", "futsal"):
        d = {{"1x": "1X", "12": "12", "x2": "X2"}[oc]: c for oc, _, c, _ in odds(g) if oc in ("1x", "12", "x2")}
        if len(d) == 3:
            mk["DC"] = d
    g = byname.get("Обе команды забьют")
    if g and sk in ("football", "futsal"):
        d = {{"yes": "Y", "no": "N"}[oc]: c for oc, _, c, _ in odds(g) if oc in ("yes", "no")}
        if len(d) == 2:
            mk["BTTS"] = d
    ot = sk in ("basketball", "am-football", "baseball")                  # в этих видах Фонбет считает фору/тотал с овертаймом
    g = pick(_OW_HCP_OT) if ot else byname.get("Фора")
    if g:
        hcp(g)
    g = pick(_OW_TOT_OT) if ot else byname.get("Тотал")
    if g:
        tot(g)
    if sk in ("football", "hockey", "futsal", "handball"):               # индивидуальные тоталы команд
        for nm, g in byname.items():
            if not nm.startswith("Индивидуальный тотал "):
                continue
            team = nm[len("Индивидуальный тотал "):].strip()
            key = "IT1" if _sim(team, home) >= _sim(team, away) else "IT2"
            d = {}
            for oc, v, c, _ in odds(g):
                t = _ol_line(v)
                if t is not None and oc in ("over", "under"):
                    d.setdefault(t, {})["O" if oc == "over" else "U"] = c
            for t, dd in d.items():
                if len(dd) == 2:
                    mk["%s:%.2f" % (key, t)] = dd
    return mk


def ow_odds(cfg, ids, timeout=40):
    """socket.io-подписка на коэффициенты: {id матча: oddsGroups}. Пачками по onewin_chunk матчей."""
    try:
        import websocket
    except ImportError:
        raise RuntimeError("нужен пакет websocket-client")
    url = "%s?Language=ru-RU&externalPartnerId=%s&EIO=4&transport=websocket" % (cfg.get("onewin_ws", OW_WS), OW_PID)
    ws = websocket.create_connection(url, timeout=15, origin="https://one-vv8027.com", header=["User-Agent: " + OW_HDR["User-Agent"]])
    res = {}
    chunk = int(cfg.get("onewin_chunk", 13))
    try:
        ws.settimeout(15)
        ws.recv()                                    # 0{sid...}
        ws.send("40")
        t_end = time.time() + timeout
        ready = False
        while not ready and time.time() < t_end:
            m = ws.recv()
            if m.startswith("40"):
                ready = True
            elif m == "2":
                ws.send("3")
        ids = list(ids)
        for i in range(0, len(ids), chunk):
            part = ids[i:i + chunk]
            ws.send("42" + json.dumps(["subscribe", {"messageType": "subscribe-match-odds", "data": {"matchIds": part, "isBaseOddsGroups": True}}]))
            want, got = set(part), set()
            t_end = time.time() + cfg.get("onewin_wait", 8)
            while got != want and time.time() < t_end:
                try:
                    m = ws.recv()
                except websocket.WebSocketTimeoutException:
                    break
                if m == "2":
                    ws.send("3")
                elif m.startswith("42"):
                    try:
                        j = json.loads(m[2:])[1]
                    except (ValueError, IndexError):
                        continue
                    if j.get("messageType") == "match-odds-snapshot":
                        d = j.get("data") or {}
                        res[d.get("matchId")] = d.get("oddsGroups") or []
                        got.add(d.get("matchId"))
            ws.send("42" + json.dumps(["unsubscribe", {"messageType": "subscribe-match-odds", "data": {"matchIds": part}}]))
    finally:
        try:
            ws.close()
        except Exception:
            pass
    return res


def onewin_fetch(cfg):
    now = time.time()
    if now < OW_CACHE["pause"]:
        return OW_CACHE["ev"]
    if OW_CACHE["ev"] and now - OW_CACHE["t"] < cfg.get("onewin_ttl", 240):
        return OW_CACHE["ev"]
    until = (now + cfg["horizon_hours"] * 3600) if cfg.get("horizon_hours") else None
    try:
        evs = []
        for sid, sk in OW_SPORTS.items():
            if sk not in cfg.get("onewin_sports", []):
                continue
            evs += ow_events(ow_list(cfg, sid, now), now, until)
        evs.sort(key=lambda e: e["start"])
        evs = evs[:int(cfg.get("onewin_max", 450))]
        odds = ow_odds(cfg, [e["bid"] for e in evs])
        n = 0
        for e in evs:
            g = odds.get(e["bid"])
            if g:
                e["markets"] = ow_markets(g, e["sk"], e["home"], e["away"])
                n += bool(e["markets"])
        total = len(evs)
        evs = [e for e in evs if e["markets"]]
        OW_CACHE.update(ev=evs, t=time.time(), fails=0, pause=0.0)
        log("1win: матчей %d, с коэффициентами %d" % (total, n))
        return evs
    except SystemExit:
        raise
    except Exception as e:
        OW_CACHE["fails"] += 1
        pause = min(900, 60 * 2 ** (OW_CACHE["fails"] - 1))
        OW_CACHE["pause"] = time.time() + pause
        log("1win недоступен: %s: %s — пауза %d с" % (type(e).__name__, e, pause))
        return OW_CACHE["ev"] if now - OW_CACHE["t"] < 1800 else []


def onewin_test(cfg):
    print("1win: проверка (только чтение)")
    cfg = dict(cfg, onewin_sports=cfg.get("onewin_sports") or ["football"], onewin_max=30)
    try:
        t0 = time.time()
        evs = onewin_fetch(cfg)
        print("матчей с коэффициентами: %d за %.1f с" % (len(evs), time.time() - t0))
        for e in evs[:8]:
            print(" ", time.strftime("%d.%m %H:%M", time.localtime(e["start"])), e["sk"], e["home"], "-", e["away"], "| рынков", len(e["markets"]),
                  {k: v for k, v in list(e["markets"].items())[:2]})
    except Exception as e:
        print("ошибка:", type(e).__name__, e)



# ============================================================ Марафон (HTML-страницы видов спорта с главными рынками)

MA_BASE = "https://www.marathonbet.ru"
MA_PAGES = {"football": "/su/betting/Football+-+11", "hockey": "/su/betting/Ice+Hockey+-+537", "basketball": "/su/betting/Basketball+-+6",
            "tennis": "/su/betting/Tennis+-+2398", "volleyball": "/su/betting/Volleyball+-+22712", "handball": "/su/betting/Handball+-+52914",
            "table-tennis": "/su/betting/Table+Tennis+-+382549", "futsal": "/su/betting/Futsal+-+444782", "esports": "/su/betting/e-Sports+-+1895085",
            "am-football": "/su/betting/American+Football+-+4", "baseball": "/su/betting/Baseball+-+5"}
MA_CACHE = {"t": 0.0, "ev": [], "pause": 0.0, "fails": 0}
MA_MONTHS = {"янв": 1, "фев": 2, "мар": 3, "апр": 4, "мая": 5, "май": 5, "июн": 6, "июл": 7, "авг": 8, "сен": 9, "окт": 10, "ноя": 11, "дек": 12}
MA_HDR = {"User-Agent": "Mozilla/5.0 (Linux; Android 14; Pixel 8) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/130.0 Mobile Safari/537.36",
          "Accept": "application/json, text/javascript, */*; q=0.01", "Accept-Language": "ru,en;q=0.9", "X-Requested-With": "XMLHttpRequest",
          "Referer": MA_BASE + "/su/"}
_MA_ROW = re.compile(r'(?=<div class="bg coupon-row")')
_MA_CELL = re.compile(r'<td[^>]*class="price[^"]*"[^>]*data-sel=\'[^\']*\'[^>]*>(.*?)</td>', re.S)
_MA_NAME = re.compile(r'data-member-link="true">([^<]+)<')
_MA_KEY = re.compile(r'data-selection-key="\d+@([^"]+)"')
_MA_PRICE = re.compile(r'data-selection-price="([\d.]+)"')
_MA_DATE = re.compile(r'date-wrapper">\s*([^<]+?)\s*<')


def ma_get(cfg, path, timeout=40):
    url = MA_BASE + path + ("&" if "?" in path else "?") + "pageAction=default&_=%d" % (time.time() * 1000)
    hdr = dict(MA_HDR)
    if cfg.get("marathon_cookie"):
        hdr["Cookie"] = cfg["marathon_cookie"]
    errs = []
    if cfg.get("marathon_curl", True) and shutil.which("curl"):
        cmd = ["curl", "-s", "-S", "--compressed", "--max-time", str(timeout), "-w", "\n%{http_code}"]
        for k, v in hdr.items():
            cmd += ["-H", "%s: %s" % (k, v)]
        r = subprocess.run(cmd + [url], capture_output=True, timeout=timeout + 10)
        b, _, code = r.stdout.rpartition(b"\n")
        if code.strip() == b"200":
            return json.loads(b)
        errs.append("curl HTTP %s" % code.strip().decode("ascii", "ignore"))
    try:
        req = urllib.request.Request(url, headers=hdr)
        with urllib.request.urlopen(req, timeout=timeout) as r:
            return json.loads(r.read().decode("utf-8", "replace"))
    except Exception as e:
        errs.append("python %s" % type(e).__name__)
    raise RuntimeError("; ".join(errs) + " [" + path + "]")


def _ma_start(txt, now, tz):
    """'25 ноя 20:45' или '20:45' (сегодня) -> unix-время (часовой пояс сайта tz, по умолчанию МСК)."""
    txt = txt.strip()
    m = re.match(r"(?:(\d{1,2})\s+([а-яё]+)\s+)?(\d{1,2}):(\d{2})$", txt)
    if not m:
        return 0
    loc = time.gmtime(now + tz * 3600)
    day, mon = (int(m.group(1)), MA_MONTHS.get(m.group(2)[:3])) if m.group(1) else (loc.tm_mday, loc.tm_mon)
    if not mon:
        return 0
    year = loc.tm_year + (1 if mon < loc.tm_mon - 6 else 0)
    try:
        return int(calendar.timegm((year, mon, day, int(m.group(3)), int(m.group(4)), 0)) - tz * 3600)
    except ValueError:
        return 0


def ma_parse(doc, sk, now=None, tz=3):
    """Ответ страницы вида спорта -> события [{bk, home, away, start, league, markets, bid, sk}]."""
    now = now or time.time()
    html_ = ""
    for blk in doc if isinstance(doc, list) else []:
        if isinstance(blk, dict) and blk.get("selector") == "#events_content":
            html_ = blk.get("content") or ""
    out = []
    for row in _MA_ROW.split(html_)[1:]:
        if 'data-live="true"' in row[:600]:
            continue
        names = [n.strip() for n in _MA_NAME.findall(row)]
        mid = re.search(r'data-event-eventId="(\d+)"', row)
        path = re.search(r'data-event-path="([^"]*)"', row)
        d = _MA_DATE.search(row)
        if len(names) < 2 or not mid or not d:
            continue
        home, away = (_html.unescape(n) for n in names[:2])
        start = _ma_start(d.group(1), now, tz)
        if start < now:
            continue
        league = urllib.parse.unquote(urllib.parse.unquote(path.group(1) if path else "")).replace("+", " ")
        league = " / ".join(league.split("/")[:-1])
        if sk != "esports" and FAKE_LEAGUE.search(league):
            continue
        mk = ma_markets(row, sk)
        if mk:
            out.append({"bk": "marathon", "home": home, "away": away, "start": start, "league": league, "markets": mk, "bid": int(mid.group(1)), "sk": sk})
    return out


def ma_markets(row, sk):
    """Коэффициенты строки матча: 1X2 / победитель, двойной шанс, фора, тотал (основные линии со страницы вида спорта)."""
    cells = []
    for c in _MA_CELL.findall(row):
        k, p = _MA_KEY.search(c), _MA_PRICE.search(c)
        if not k or not p:
            continue
        pre = c.split("<span", 1)[0]
        ln = re.search(r"\(([^()]*)\)", pre)
        try:
            v = float(p.group(1))
        except ValueError:
            continue
        if v > 1.0:
            cells.append((k.group(1), v, ln.group(1).strip() if ln else None))
    mk, w3, ml, dc, hc, tt = {}, {}, {}, {}, {}, {}
    for key, v, ln in cells:
        name, _, suf = key.partition(".")
        name = name.rstrip("0123456789")                      # у хоккея «Result0», «Total_Goals0»
        if name in ("Match_Result", "Result") and suf in ("1", "draw", "3"):
            w3[suf] = v
        elif name in ("Match_Winner", "To_Win_Match", "Match_Winner_Including_All_OT") and suf in ("1", "3", "HB_H", "HB_A"):
            ml[{"1": "1", "HB_H": "1", "3": "2", "HB_A": "2"}[suf]] = v
        elif name in ("Result", "Double_Chance") and suf in ("HD", "HA", "AD", "DA"):
            dc[{"HD": "1X", "HA": "12", "AD": "X2", "DA": "X2"}[suf]] = v
        elif suf in ("HB_H", "HB_A") and ("Handicap" in name or name == "Points_Spread") and "By_Legs" not in name and "Frames" not in name:
            h = _ol_line(ln.replace("+", "")) if ln and "," not in ln else None
            if h is not None:
                hc.setdefault((name, h if suf == "HB_H" else -h), {})["1" if suf == "HB_H" else "2"] = v
        elif name.startswith("Total_") and (suf.startswith("Under_") or suf.startswith("Over_")):
            t = _ol_line(suf.split("_", 1)[1])
            if t is not None and "Legs" not in name and "Frames" not in name:
                tt.setdefault((name, t), {})["U" if suf.startswith("Under") else "O"] = v
    if len(w3) == 3 and sk in ("football", "hockey", "handball", "futsal"):
        mk["1X2"] = {"1": w3["1"], "X": w3["draw"], "2": w3["3"]}
    elif "1" in w3 and "3" in w3 and "draw" not in w3:
        ml.setdefault("1", w3["1"])
        ml.setdefault("2", w3["3"])
    if len(ml) == 2 and (sk != "football"):
        mk["ML"] = ml
    if len(dc) == 3 and sk in ("football", "hockey", "handball", "futsal"):
        mk["DC"] = dc
    for (_, line), d in hc.items():
        if len(d) == 2 and abs(line) >= _OL_MIN_HCP.get(sk, 0):
            mk["HCP:%.2f" % (line + 0.0)] = d
    for (_, t), d in tt.items():
        if len(d) == 2 and t >= _OL_MIN_TOTAL.get(sk, 0):
            mk["TOTAL:%.2f" % t] = d
    return mk if sk != "esports" else {k: v for k, v in mk.items() if k == "ML"}


def marathon_fetch(cfg):
    now = time.time()
    if now < MA_CACHE["pause"]:
        return MA_CACHE["ev"]
    if MA_CACHE["ev"] and now - MA_CACHE["t"] < cfg.get("marathon_ttl", 240):
        return MA_CACHE["ev"]
    out, ok, bad = [], 0, 0
    until = (now + cfg["horizon_hours"] * 3600) if cfg.get("horizon_hours") else None
    pages = dict(MA_PAGES)
    pages.update(cfg.get("marathon_pages") or {})
    for sk in cfg.get("marathon_sports", []):
        path = pages.get(sk)
        if not path:
            continue
        try:
            evs = ma_parse(ma_get(cfg, path), sk, now, cfg.get("marathon_tz", 3))
            out += [e for e in evs if not until or e["start"] <= until]
            ok += 1
        except SystemExit:
            raise
        except Exception as e:
            bad += 1
            log("Марафон (%s): %s: %s" % (sk, type(e).__name__, e))
        time.sleep(cfg.get("marathon_gap", 1.0))
    if not ok:
        MA_CACHE["fails"] += 1
        pause = min(900, 60 * 2 ** (MA_CACHE["fails"] - 1))
        MA_CACHE["pause"] = time.time() + pause
        log("Марафон недоступен — пауза %d с" % pause)
        return MA_CACHE["ev"] if now - MA_CACHE["t"] < 1800 else []
    MA_CACHE.update(ev=out, t=time.time(), fails=0, pause=0.0)
    log("Марафон: матчей %d (видов спорта %d, ошибок %d)" % (len(out), ok, bad))
    return out


def marathon_test(cfg):
    print("Марафон: проверка (только чтение)")
    cfg = dict(cfg, marathon_sports=cfg.get("marathon_sports") or ["football", "tennis"])
    try:
        evs = marathon_fetch(cfg)
        print("матчей: %d" % len(evs))
        for e in evs[:8]:
            print(" ", time.strftime("%d.%m %H:%M", time.localtime(e["start"])), e["sk"], e["home"], "-", e["away"], "|", e["league"][:40], "| рынков", len(e["markets"]),
                  {k: v for k, v in list(e["markets"].items())[:2]})
    except Exception as e:
        print("ошибка:", type(e).__name__, e)



# ============================================================ настройки парсера с сайта (settings.json в ветке данных GitHub)

SET_STATE = {"etag": None, "ok": 0.0}


def _bk_odds_clean(d):
    out = {}
    if isinstance(d, dict):
        for bk, r in d.items():
            if bk not in BK_TITLE or not isinstance(r, dict):
                continue
            try:
                lo, hi = float(r.get("min") or 0), float(r.get("max") or 0)
            except (TypeError, ValueError):
                continue
            lo, hi = max(0.0, lo), max(0.0, hi)
            if lo or hi:
                out[bk] = {"min": round(lo, 3), "max": round(hi, 3)}
    return out


def _settings_file():
    return os.path.join(os.path.dirname(USERS.path), "settings_remote.json")


def _bk_odds_txt(d):
    return "; ".join("%s %s" % (BK_TITLE[b], ("%.2f–%.2f" % (r["min"], r["max"])) if r["min"] and r["max"]
                                 else ("от %.2f" % r["min"]) if r["min"] else ("до %.2f" % r["max"])) for b, r in d.items()) or "без ограничений"


def settings_txt(cfg):
    return "фрибет — %s; денежные — %s" % (_bk_odds_txt(cfg.get("bk_odds") or {}), _bk_odds_txt(cfg.get("bk_odds_cash") or {}))


def _days_clean(v):
    try:
        d = int(float(v))
    except (TypeError, ValueError):
        return 0
    return d if 1 <= d <= 14 else 0


def settings_apply(cfg, data, src):
    new = _bk_odds_clean((data or {}).get("bk_odds"))
    newc = _bk_odds_clean((data or {}).get("bk_odds_cash"))
    days = _days_clean((data or {}).get("horizon_days"))
    same_days = (not days) or cfg.get("horizon_hours") == days * 24
    if new == (cfg.get("bk_odds") or {}) and newc == (cfg.get("bk_odds_cash") or {}) and same_days:
        return False
    cfg["bk_odds"], cfg["bk_odds_cash"] = new, newc
    if days:
        cfg["horizon_hours"] = days * 24
        cfg["betcity_hours"] = 24 if days <= 1 else 48 if days == 2 else 72    # Бетсити отдаёт счётчики только на 24/48/72 ч
    log("настройки парсера (%s): коэффициенты: %s; горизонт: %s" % (src, settings_txt(cfg), ("%d дн." % days) if days else "как в config"))
    try:
        with open(_settings_file(), "w", encoding="utf-8") as fh:
            json.dump({"bk_odds": new, "bk_odds_cash": newc, "horizon_days": days}, fh, ensure_ascii=False)
    except OSError:
        pass
    return True


def settings_restore(cfg):
    """При старте: прошлые настройки с сайта (если телефон был выключен или GitHub недоступен)."""
    try:
        with open(_settings_file(), encoding="utf-8") as fh:
            settings_apply(cfg, json.load(fh), "сохранённые")
    except (OSError, ValueError):
        pass


def settings_sync(cfg):
    """Читает settings.json из ветки данных (раз в settings_poll сек). True — настройки изменились."""
    if not (cfg.get("web_repo") and cfg.get("web_token")):
        return False
    hdr = {"Authorization": "Bearer " + cfg["web_token"], "Accept": "application/vnd.github.raw+json", "User-Agent": "arbphone",
           "X-GitHub-Api-Version": "2022-11-28"}
    if SET_STATE["etag"]:
        hdr["If-None-Match"] = SET_STATE["etag"]
    req = urllib.request.Request("https://api.github.com/repos/%s/contents/settings.json?ref=%s" % (cfg["web_repo"], cfg["web_branch"]), headers=hdr)
    try:
        with urllib.request.urlopen(req, timeout=20) as r:
            SET_STATE["etag"] = r.headers.get("ETag")
            return settings_apply(cfg, json.loads(r.read().decode("utf-8", "replace")), "сайт")
    except urllib.error.HTTPError as e:
        if e.code in (304, 404):
            return False
        raise


def settings_loop(cfg):
    while True:
        time.sleep(max(10, cfg.get("settings_poll", 30)))
        try:
            if settings_sync(cfg):
                REFRESH.set()                                      # сразу пересчитать вилки
                try:
                    tg_send(cfg, "⚙ <b>Настройки парсера изменены с сайта</b>\nКоэффициенты: %s\nПересчитываю вилки." % settings_txt(cfg))
                except Exception:
                    pass
        except Exception as e:
            log("настройки с сайта: %s: %s" % (type(e).__name__, e))


def _norm(s):
    s = re.sub(r"\s+[А-ЯЁ]{2}$", "", s.strip())    # суффикс региона у Винлайна: «ПР», «СП»
    s = s.lower().replace("ё", "е")
    s = re.sub(r"\(ж\)|\bжен\w*", "", s)
    s = re.sub(r"[^\w\s]", " ", s)
    return re.sub(r"\s+", " ", s).strip()


def _flags(s):
    l = s.lower()
    f = set()
    if "(ж)" in l or "жен" in l:
        f.add("w")
    f.update(re.findall(r"\bu-?(\d\d)\b", l))
    if "резерв" in l or re.search(r"\bii\b", l):
        f.add("r")
    return f


def _sim(a, b):
    return difflib.SequenceMatcher(None, _norm(a), _norm(b)).ratio()


def match_events(win, fon):
    idx = collections.defaultdict(list)
    for f in fon:
        idx[f["start"] // 60].append(f)
    used, pairs = set(), []
    for w in win:
        m0 = w["start"] // 60
        best = None
        for d in range(-5, 6):
            for f in idx.get(m0 + d, []):
                if f["id"] in used:
                    continue
                for swapped in (False, True):
                    h2, a2 = (f["away"], f["home"]) if swapped else (f["home"], f["away"])
                    if _flags(w["home"]) != _flags(h2) or _flags(w["away"]) != _flags(a2):
                        continue
                    s1, s2 = _sim(w["home"], h2), _sim(w["away"], a2)
                    sc = min(s1, s2)
                    lim = 0.0 if f.get("sk", "football") == "football" else 0.12
                    if sc >= 0.62 + lim and (s1 + s2) / 2 >= 0.7 + lim and (best is None or sc > best[0]):
                        best = (sc, f, swapped)
        if best:
            used.add(best[1]["id"])
            pairs.append((w, best[1], best[2]))
    return pairs


# ============================================================ вилки

def _split(key):
    """Ключ рынка -> (префикс периода/вида "1H:CRN:", остаток: 1X2 / TOTAL:L / HCP:L / BTTS / DC)."""
    pre = ""
    for t in ("1H:", "2H:", "CRN:"):
        if key.startswith(t):
            pre += t
            key = key[len(t):]
    return pre, key


def _flip(mk):
    """Матч у второй БК записан с хозяевами и гостями наоборот: переворачиваем рынки."""
    out = {}
    for key, d in mk.items():
        pre, k = _split(key)
        if k == "1X2":
            out[pre + k] = {"1": d["2"], "X": d["X"], "2": d["1"]}
        elif k == "ML":
            out[k] = {"1": d["2"], "2": d["1"]}
        elif k.startswith("IT1:"):
            out[pre + "IT2:" + k[4:]] = d
        elif k.startswith("IT2:"):
            out[pre + "IT1:" + k[4:]] = d
        elif k.startswith("HCP:"):
            out[pre + "HCP:%.2f" % (-float(k[4:]) + 0.0)] = {"1": d["2"], "2": d["1"]}
        elif k == "DC":
            out[k] = {"1X": d["X2"], "X2": d["1X"], "12": d["12"]}
        else:
            out[pre + k] = d
    return out


def _hcp_abs(key):
    pre, k = _split(key)
    if not k.startswith("HCP:"):
        return 0.0
    return abs(float(k[4:])) * (0.5 if "CRN:" in pre else 1.0)   # у угловых линии вдвое больше (лимит как для голов)


def _build(base, opts, cfg, res, freebets=True):
    """opts: исход -> [(коэффициент, БК), ...]. Добавляет в res денежную и фрибетные вилки (БК может быть любое число)."""
    crng = cfg.get("bk_odds_cash") or {}
    copts = opts
    if crng:                                                          # границы коэффициентов для ДЕНЕЖНЫХ вилок (с сайта)
        copts = {o: [(v, b) for v, b in lst if crng.get(b, {}).get("min", 0) <= v <= (crng.get(b, {}).get("max") or 1e9)] for o, lst in opts.items()}
    best = {o: max(v) for o, v in copts.items()} if all(copts.values()) else {}
    if best and len({b for _, b in best.values()}) >= 2:
        inv = sum(1.0 / v for v, _ in best.values())
        stakes = [(o, bk, v, cfg["bank"] * (1.0 / v) / inv) for o, (v, bk) in best.items()]
        res.append(dict(base, mode="cash", pct=(1.0 / inv - 1.0) * 100.0, stakes=stakes,
                        profit=cfg["bank"] / inv - cfg["bank"], base_sum=cfg["bank"]))
    if not freebets:
        return
    rng = cfg.get("bk_odds") or {}
    if rng:                                                           # границы коэффициента по БК (с сайта) — только для фрибетных вилок; денежные берут любые
        opts = {o: [(v, b) for v, b in lst if rng.get(b, {}).get("min", 0) <= v <= (rng.get(b, {}).get("max") or 1e9)] for o, lst in opts.items()}
        if any(not lst for lst in opts.values()):
            return
    F = cfg["freebet_size"] or 1000.0
    books = sorted({b for lst in opts.values() for _, b in lst})
    for fb in books:
        if fb == "polymarket":
            continue
        rule = (cfg.get("fb_rules") or {}).get(fb) or {}                 # правило фрибета: фрибет-ставка от min, ставки против — только на «vs» и до vs_max
        for scope in [""] + ([b for b in books if b != fb] if len(books) > 2 and not rule else []):         # "" = противоположные ставки где угодно, иначе — только на этом БК
            found = []
            for a, lst in opts.items():
                own = [v for v, b in lst if b == fb and v >= rule.get("min", 0)]
                if not own:
                    continue
                t = F * (max(own) - 1.0)
                hedge, ok = [], True
                for o, ol in opts.items():
                    if o == a:
                        continue
                    oth = [(v, b) for v, b in ol if b != fb and (not scope or b == scope)
                           and (not rule.get("vs") or b == rule["vs"]) and v <= rule.get("vs_max", 1e9)]
                    if not oth:
                        ok = False
                        break
                    v, b = max(oth)
                    hedge.append((o, b, v, t / v))
                if not ok:
                    continue
                prof = t - sum(h[3] for h in hedge)
                conv = prof / F * 100.0
                found.append(dict(base, mode="freebet", fb_bk=fb, pct=conv, profit=prof, base_sum=F,
                                  stakes=[(a, fb, max(own), F)] + hedge))
            if found:
                found.sort(key=lambda r: -r["pct"])
                res.append(found[0])
                res.extend(r for r in found[1:] if r["pct"] >= cfg["min_conv"])    # другие исходы под фрибет — для фильтра по коэффициенту


DC_COMBOS = (("1X", "2"), ("X2", "1"), ("12", "X"))


def _spread(books, outs):
    """Макс. |ln| расхождения коэффициентов между БК по исходам (признак ошибки разбора)."""
    d = 0.0
    for o in outs:
        v = [b[o] for b in books if o in b]
        if len(v) >= 2:
            d = max(d, math.log(max(v) / min(v)))
    return d


WIDE = {"basketball", "am-football", "volleyball", "table-tennis", "tennis"}


def _cross_lines(f, mk, cfg, res):
    """Вилки с РАЗНЫМИ линиями (коридор / перекрытие). Тотал: «больше L1» + «меньше L2» при L2 > L1 — при любом счёте
    выигрывает минимум одна ставка (при L1 < итог < L2 обе). Фора: ставка на хозяев с линией h + ставка на гостей
    при линии хозяев h2 < h (т.е. гости получают -h2) — тоже покрывают все исходы; на границе целой линии ставка возвращается."""
    gap = cfg.get("max_line_gap", 2.0) * (2.5 if f.get("sk") in WIDE else 1.0)
    tot, hcp = collections.defaultdict(dict), collections.defaultdict(dict)
    for bk, m in mk.items():
        for key, d in m.items():
            pre, k = _split(key)
            if k.startswith(("TOTAL:", "IT1:", "IT2:")):
                fam = k.split(":")[0]
                tot[(pre, fam)].setdefault(float(k.split(":")[1]), {})[bk] = d
            elif k.startswith("HCP:"):
                hcp[pre].setdefault(float(k[4:]), {})[bk] = d
    foot = f.get("sk", "football") == "football"
    for (pre, fam), lines in tot.items():
        for l1, b1 in lines.items():
            for l2, b2 in lines.items():
                if not (0 < l2 - l1 <= gap):
                    continue
                over = [(d["O"], bk) for bk, d in b1.items()]
                under = [(d["U"], bk) for bk, d in b2.items()]
                if len({b for _, b in over + under}) < 2:
                    continue
                inv = 1.0 / max(over)[0] + 1.0 / max(under)[0]
                if inv > 1.15:
                    continue
                base = {"event": f, "fon": f, "key": "%s%s2:%g:%g" % (pre, fam, l1, l2), "div": 0.0}
                _build(base, {"O": over, "U": under}, cfg, res, freebets=False)
    for pre, lines in hcp.items():
        for h, bh in lines.items():
            for h2, bg in lines.items():
                if not (0 < h - h2 <= gap):
                    continue
                if foot and max(abs(h), abs(h2)) * (0.5 if "CRN:" in pre else 1.0) > cfg["max_hcp_line"]:
                    continue
                home = [(d["1"], bk) for bk, d in bh.items()]
                away = [(d["2"], bk) for bk, d in bg.items()]
                if len({b for _, b in home + away}) < 2:
                    continue
                if 1.0 / max(home)[0] + 1.0 / max(away)[0] > 1.15:
                    continue
                base = {"event": f, "fon": f, "key": "%sHCP2:%g:%g" % (pre, h, h2), "div": 0.0}
                _build(base, {"1": home, "2": away}, cfg, res, freebets=False)


def find_arbs(groups, cfg):
    """groups: [{"f": матч Фонбета, "mk": {БК: рынки в ориентации Фонбета}}]. Возвращает кандидатов (включая убыточные)."""
    res = []
    for g in groups:
        f, mk = g["f"], g["mk"]
        if len(mk) < 2:
            continue
        keys = set()
        for m in mk.values():
            keys.update(k for k in m if k != "DC")
        for key in keys:
            have = {bk: m[key] for bk, m in mk.items() if key in m}
            if len(have) < 2 or (f.get("sk", "football") == "football" and _hcp_abs(key) > cfg["max_hcp_line"]):
                continue
            outs = set(next(iter(have.values())))
            have = {bk: d for bk, d in have.items() if set(d) == outs}
            if len(have) < 2:
                continue
            base = {"event": f, "fon": f, "key": key, "div": _spread(list(have.values()), outs)}
            _build(base, {o: [(d[o], bk) for bk, d in have.items()] for o in outs}, cfg, res)
        _cross_lines(f, mk, cfg, res)
        # двойной шанс (Фонбет, БетБум) против одиночного исхода 1X2 любой БК
        for pre in ("", "1H:", "2H:"):
            dcs = {bk: m[pre + "DC"] for bk, m in mk.items() if pre + "DC" in m}
            x12 = {bk: m[pre + "1X2"] for bk, m in mk.items() if pre + "1X2" in m}
            if dcs and x12:
                div = max(_spread(list(x12.values()), ("1", "X", "2")), _spread(list(dcs.values()), ("1X", "X2", "12")))
                for d, single in DC_COMBOS:
                    base = {"event": f, "fon": f, "key": "%sDC:%s|%s" % (pre, d, single), "div": div}
                    _build(base, {d: [(v[d], bk) for bk, v in dcs.items()],
                                  single: [(v[single], bk) for bk, v in x12.items()]}, cfg, res)
    return sorted(res, key=lambda r: r["pct"], reverse=True)


def sort_key(a):
    """Сначала вилки на 2 исхода, затем на 3; внутри — ближайшие по времени матча, при равенстве — выгоднее."""
    return (len(a["stakes"]), a["event"]["start"], -a["pct"])


def acceptable(a, cfg):
    if a["div"] > cfg["max_diverge"]:
        return False
    if a["mode"] == "cash":
        return cfg["min_profit"] <= a["pct"] <= cfg["max_profit"]
    return a["pct"] >= cfg["min_conv"]


# ============================================================ сообщение

def esc(s):
    return s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def _line(L):
    return "0" if L == 0 else "%+g" % L


USD_CACHE = {"t": 0.0, "v": None}


def usd_rate(cfg):
    """Курс доллара к рублю: usd_rub из config.json или (если 0) курс ЦБ РФ, обновляется раз в 6 часов. None — неизвестен."""
    v = _pm_f(cfg.get("usd_rub")) if cfg else None
    if v and v > 0:
        return v
    if USD_CACHE["v"] and time.time() - USD_CACHE["t"] < 21600:
        return USD_CACHE["v"]
    try:
        d = json.loads(http_get("https://www.cbr-xml-daily.ru/daily_json.js", {"User-Agent": UA}, 15))
        USD_CACHE["v"], USD_CACHE["t"] = float(d["Valute"]["USD"]["Value"]), time.time()
    except Exception as e:
        log("курс доллара не получен: %s: %s" % (type(e).__name__, e))
        USD_CACHE["t"] = time.time() - 21600 + 300          # повтор через 5 минут
    return USD_CACHE["v"]


USD_BKS = ("polymarket", "onewin")                        # суммы на этих БК показываем в долларах


def stake_txt(cfg, bk, rub):
    """Сумма ставки: на Polymarket и 1win — в долларах (и в рублях в скобках), на остальных БК — в рублях."""
    if bk in USD_BKS:
        r = usd_rate(cfg)
        if r:
            return "$%.2f (≈ %s ₽)" % (rub / r, _money(rub))
        return "%s ₽ (курс $ неизвестен — задайте usd_rub в config.json)" % _money(rub)
    return "%s ₽" % _money(rub)


def en_label(a, o):
    pm = a["event"].get("pm")
    if not pm:
        return None
    h, g = esc(pm[0]), esc(pm[1])
    k = _split(a["key"])[1]
    if k in ("1X2", "ML"):
        return {"1": "Win: %s" % h, "X": "Draw", "2": "Win: %s" % g}.get(o)
    if k == "BTTS":
        return "Both teams to score: %s" % ("Yes" if o == "Y" else "No")
    m2 = re.match(r"TOTAL(2?):([^:]+)(?::(.+))?$", k)
    if m2:
        cross, l1, l2 = m2.groups()
        line = float(l1) if o == "O" or not cross else float(l2)
        return "Total %s %g" % ("Over" if o == "O" else "Under", line)
    return None


def bet_label(a, o, bk=None):
    ru = _bet_label(a, o)
    if bk == "polymarket":
        en = en_label(a, o)
        if en:
            return "%s (%s)" % (en, ru)
    return ru


def _bet_label(a, o):
    h, g, key = esc(a["event"]["home"]), esc(a["event"]["away"]), a["key"]
    hm = h
    p0, k = _split(key)
    pre = {"": "", "1H:": "1-й тайм: ", "2H:": "2-й тайм: ", "CRN:": "Угловые: ", "1H:CRN:": "1-й тайм, угловые: ",
           "2H:CRN:": "2-й тайм, угловые: "}[p0]
    if k.startswith("DC:"):
        dcn = {"1X": "Двойной шанс: %s или ничья" % h, "X2": "Двойной шанс: ничья или %s" % g,
               "12": "Двойной шанс: %s или %s" % (h, g)}
        if o in dcn:
            return pre + dcn[o]
        return pre + {"1": "Победа %s" % h, "X": "Ничья", "2": "Победа %s" % g}[o]
    m2 = re.match(r"(TOTAL|IT1|IT2)(2?):([^:]+)(?::(.+))?$", k)
    if m2:
        fam, cross, l1, l2 = m2.groups()
        line = float(l1) if o == "O" or not cross else float(l2)
        who = {"TOTAL": "", "IT1": " " + h, "IT2": " " + g}[fam]
        return pre + "%s%s %s %g" % ("Тотал" if fam == "TOTAL" else "Индивидуальный тотал", who,
                                    "больше" if o == "O" else "меньше", line)
    if k in ("1X2", "ML"):
        return pre + {"1": "Победа %s" % h, "X": "Ничья", "2": "Победа %s" % g}[o]
    if k == "BTTS":
        return pre + "Обе забьют: %s" % ("да" if o == "Y" else "нет")
    if k.startswith("HCP2:"):
        _, h, h2 = k.split(":")
        return pre + ("Фора %s (%s)" % (hm, _line(float(h))) if o == "1" else "Фора %s (%s)" % (g, _line(-float(h2))))
    if k.startswith("TOTAL:"):
        return pre + "Тотал %s %g" % ("больше" if o == "O" else "меньше", float(k[6:]))
    L = float(k[4:])
    return pre + ("Фора %s (%s)" % (h, _line(L)) if o == "1" else "Фора %s (%s)" % (g, _line(-L)))


def _money(x):
    r = round(x)
    return "{:,}".format(0 if r == 0 else r).replace(",", " ")


def fmt_age(s):
    s = int(s)
    if s < 60:
        return "меньше минуты"
    if s < 3600:
        return "%d мин" % (s // 60)
    return "%d ч %d мин" % (s // 3600, (s % 3600) // 60)


ORD = ["первом", "втором"]


def render(a, cfg, data_age, arb_age):
    """Информационное сообщение о вилке (без сумм ставок — их считает кнопка «Рассчитать»)."""
    ev = a["event"]
    start = dt.datetime.fromtimestamp(ev["start"], MSK).strftime("%d/%m %H:%M")
    cash = a["mode"] == "cash"
    head = "💰 <b>ВИЛКА</b>" if cash else "🎁 <b>ФРИБЕТ</b> (%s)" % BK_TITLE[a["fb_bk"]]
    lines = [head]
    if cash and a["pct"] > 5:
        lines.append("⚠️ Высокая вилка — перед ставкой проверьте коэффициенты вручную")
    lines += ["Событие: <code>%s – %s</code>" % (esc(ev["home"]), esc(ev["away"])),
              "Вид спорта: %s" % esc(a["fon"].get("sport") or "Футбол"), "Лига/Чемпионат: %s" % esc(a["fon"]["league"]),
              "Дата начала события: %s МСК" % start,
              "Возраст вилки: %s" % fmt_age(arb_age)]
    if cash:
        lines.append("Прибыль: <b>%.2f%%</b>" % a["pct"])
    lines.append("Букмекеры: %s" % " - ".join(dict.fromkeys(BK_TITLE[b] for _, b, _, _ in a["stakes"])))
    n = len(a["stakes"])
    if not cash:                                # формат по образцу: событие для фрибета / противоположная ставка / сумма
        rows, hedge, _t, prof, pct = calc(a, a["base_sum"])
        lines.append("Размер фрибета: %s Руб." % _money(a["base_sum"]))
        o, bk, v, _ = rows[0]
        lines.append("Событие для фрибета: %s коэффициент - <b>%.2f</b> (%s)" % (bet_label(a, o, bk), v, BK_TITLE[bk]))
        for i, (o, bk, v, st) in enumerate(rows[1:], 1):
            lines.append("Противоположная ставка%s: %s коэффициент - <b>%.2f</b> (%s)" %
                         ("" if n == 2 else " %d" % i, bet_label(a, o, bk), v, BK_TITLE[bk]))
        for o, bk, v, st in rows[1:]:
            if bk in USD_BKS:
                lines.append("Ставить на %s: <b>%s</b>" % (BK_TITLE[bk], stake_txt(cfg, bk, st)))
        lines += ["Сумма противоположной ставки: %.2f" % hedge, "Доходность в процентах: <b>%.2f%%</b>" % pct,
                  "Прибыль: <b>%.2f Руб.</b>" % prof]
        return "\n\n".join(lines)
    for i, (o, bk, v, _st) in enumerate(a["stakes"]):
        who = ("Ставка на %s букмекере" % ORD[i]) if n == 2 else ("Ставка %d (%s)" % (i + 1, BK_TITLE[bk]))
        lines.append("%s: %s - коэффициент - <b>%.2f</b>" % (who, bet_label(a, o, bk), v))
    return "\n\n".join(lines)               # пустая строка между всеми строками, как в образце


# ---------- калькулятор (как на сайтах-калькуляторах вилок)

def calc(a, amount):
    """Денежная: amount = сумма первой ставки; выплата одинакова при любом исходе.
    Фрибет: amount = размер фрибета; ставка на фрибет не возвращается, остальные ставки хеджируют выигрыш."""
    st = a["stakes"]
    if a["mode"] == "cash":
        payout = amount * st[0][2]
        rows = [(o, bk, v, payout / v) for o, bk, v, _ in st]
        total = sum(r[3] for r in rows)
        return rows, total, payout, payout - total, (payout - total) / total * 100.0
    t = amount * (st[0][2] - 1.0)
    rows = [(st[0][0], st[0][1], st[0][2], amount)] + [(o, bk, v, t / v) for o, bk, v, _ in st[1:]]
    hedge = sum(r[3] for r in rows[1:])
    return rows, hedge, t, t - hedge, (t - hedge) / amount * 100.0


def render_calc(a, amount, seen_ago, cfg=None):
    """Короткий блок под вилкой: на какой БК, на что, по какому коэффициенту и сколько ставить."""
    rows, spent, payout, profit, pct = calc(a, amount)
    lines = ["🧮 <b>Расчёт на %s ₽</b>%s" % (_money(amount), " (фрибет)" if a["mode"] == "freebet" else "")]
    for i, (o, bk, v, st) in enumerate(rows, 1):
        tag = " (фрибет)" if a["mode"] == "freebet" and i == 1 else ""
        lines.append("%d) %s — %s @ <b>%.2f</b> → <b>%s</b>%s" % (i, BK_TITLE[bk], bet_label(a, o, bk), v, stake_txt(cfg, bk, st), tag))
    lines.append("Прибыль: <b>%s ₽</b> (%.1f%%)" % (_money(profit), pct))
    if seen_ago > 150:
        lines.append("⚠️ Вилка уже пропала из выдачи — коэффициенты устарели")
    return "\n".join(lines)


# ============================================================ Telegram

def tg_api(cfg, method, payload, timeout=20):
    req = urllib.request.Request("https://api.telegram.org/bot%s/%s" % (cfg["bot_token"], method),
                                 data=json.dumps(payload).encode(), headers={"Content-Type": "application/json"})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return json.loads(r.read())


def tg_send2(cfg, text, markup=None, chat=None):
    """-> (успех, код ошибки). 403 = пользователь заблокировал бота."""
    if not cfg["bot_token"] or not (chat or cfg["chat_id"]):
        return False, -1
    payload = {"chat_id": chat or cfg["chat_id"], "text": text, "parse_mode": "HTML", "disable_web_page_preview": True}
    if markup:
        payload["reply_markup"] = markup
    for attempt in (1, 2):
        try:
            tg_api(cfg, "sendMessage", payload)
            return True, 0
        except urllib.error.HTTPError as e:
            if e.code == 429 and attempt == 1:                   # лимит Telegram: ждём сколько просит и повторяем
                try:
                    time.sleep(min(30, json.loads(e.read())["parameters"]["retry_after"] + 1))
                    continue
                except Exception:
                    pass
            log("Telegram HTTP", e.code)                         # токен в лог не пишем
            return False, e.code
        except Exception as e:
            log("Telegram:", type(e).__name__)
            return False, -1
    return False, 429


def tg_send(cfg, text, markup=None, chat=None):
    return tg_send2(cfg, text, markup, chat)[0]


def btn(text, data):
    return {"text": text, "callback_data": data}


def kb_alert(aid):
    return {"inline_keyboard": [[btn("🧮 Рассчитать", "calc:" + aid)], [btn("📋 Меню", "home")]]}


# ============================================================ пользователи бота

class Users:
    """Подписчики: chat_id -> настройки. Хранится в users.json рядом со скриптом."""

    def __init__(self, path):
        self.lock = threading.RLock()
        self.path, self.d = path, {}
        try:
            with open(path, encoding="utf-8") as fh:
                self.d = json.load(fh)
        except Exception:
            self.d = {}

    def save(self):
        with self.lock:
            try:
                tmp = self.path + ".tmp"
                with open(tmp, "w", encoding="utf-8") as fh:
                    json.dump(self.d, fh, ensure_ascii=False, indent=1)
                os.replace(tmp, self.path)
            except Exception as e:
                log("users.json:", type(e).__name__)

    def get(self, chat):
        with self.lock:
            return self.d.get(str(chat))

    def add(self, cfg, chat, name):
        """Регистрирует (или возвращает в подписчики). -> True, если пользователь новый."""
        with self.lock:
            u, new = self.d.get(str(chat)), False
            if u is None:
                u = {"name": name, "joined": int(time.time()), "cash": True, "min_profit": float(cfg["min_profit"]),
                     "push": False, "fb_auto": bool(cfg["freebet_auto"]), "fb_bk": cfg["freebet_bk"],
                     "min_conv": float(cfg["min_conv_push"])}
                self.d[str(chat)] = u
                new = True
            u["active"] = True
            self.save()
            return new

    def active(self):
        with self.lock:
            return [(c, dict(u)) for c, u in self.d.items() if u.get("active")]

    def set(self, chat, **kw):
        with self.lock:
            if str(chat) in self.d:
                self.d[str(chat)].update(kw)
                self.save()


USERS = Users("users.json")
REFRESH = threading.Event()
BC_CACHE = {"t": 0.0, "ev": []}
LEON_CACHE = {"t": 0.0, "ev": []}
LEON_LG = {}                                 # id лиги -> {id, name, sport{family,name}} из списка видов спорта
CYC = {"start": 0, "done": 0}


def wants(u, a):
    """Подходит ли вилка настройкам пользователя."""
    if a["mode"] == "cash":
        return u.get("cash", True) and a["pct"] >= u.get("min_profit", 0)
    return u.get("fb_auto") and a["pct"] >= u.get("min_conv", 70) and u.get("fb_bk", "") in ("", a["fb_bk"])


# ============================================================ хранилище найденных вилок (для меню)

def arb_id(a):
    key = "|".join([a["mode"], a.get("fb_bk", ""), a["event"]["home"], a["event"]["away"],
                    str(a["event"]["start"] // 1800), a["key"]] + ["%s:%s" % (bk, o) for o, bk, _, _ in a["stakes"]])
    return hashlib.md5(key.encode()).hexdigest()[:10]


class Store:
    def __init__(self):
        self.lock = threading.RLock()
        self.cash, self.fb, self.fball = [], {b: [] for b in BKS}, []
        self.by_id, self.first = {}, {}        # id -> (вилка, когда видели последний раз); id -> [впервые, последний раз]
        self.info, self.best, self.updated = "ещё не было цикла", None, 0.0

    def update(self, cands, cfg, now, t_data, info):
        with self.lock:
            cash = [a for a in cands if a["mode"] == "cash" and a["div"] <= cfg["max_diverge"] and a["pct"] >= -60.0]   # включая убыточные: фильтр у каждого свой
            fb = {b: [] for b in BKS}
            for a in cands:
                if a["mode"] == "freebet" and acceptable(a, cfg):
                    fb[a["fb_bk"]].append(a)
            for a in cash + [x for v in fb.values() for x in v]:
                a["id"], a["t_data"] = arb_id(a), t_data
                f = self.first.get(a["id"])
                if f:
                    f[1] = now
                else:
                    self.first[a["id"]] = [now, now]
                self.by_id[a["id"]] = (a, now)
            for k in [k for k, f in self.first.items() if now - f[1] > 300]:
                del self.first[k]
            for k in [k for k, (_, t) in self.by_id.items() if now - t > 6 * 3600]:
                del self.by_id[k]
            cash.sort(key=sort_key)
            for lst in fb.values():
                lst.sort(key=sort_key)
            self.cash = cash
            uniq = {}
            for v in fb.values():
                for a in v:
                    uniq.setdefault(a["id"], a)                     # одинаковые вилки из разных «областей» хеджа — одна
            self.fball = sorted(uniq.values(), key=sort_key)
            self.fb = {k: v[:30] for k, v in fb.items()}
            self.best = next((a for a in cands if a["mode"] == "cash" and a["div"] <= cfg["max_diverge"]), None)
            self.info, self.updated = info, now

    def age(self, aid, now):
        with self.lock:
            f = self.first.get(aid)
            return now - f[0] if f else 0


STORE = Store()
VIEWS = {}


def view(chat):
    return VIEWS.setdefault(str(chat), {"ids": [], "pos": 0, "title": "", "last": None, "pending": None})


# ============================================================ меню-бот (getUpdates)

def kb_menu(admin=False):
    rows = [[btn("💰 Денежные вилки", "cash"), btn("🎁 Фрибетные вилки", "fb")],
            [btn("⚙️ Настройки", "set"), btn("📊 Статус", "stat")],
            [btn("🌐 Сайт", "site"), btn("🔄 Обновить данные", "refresh")]]
    if admin:
        rows.append([btn("🛠 Админ-панель", "adm")])
    return {"inline_keyboard": rows}


def kb_fb():
    return {"inline_keyboard": [[btn(BK_TITLE[b], "fb1:" + b) for b in FB_BKS[:3]], [btn(BK_TITLE[b], "fb1:" + b) for b in FB_BKS[3:]],
                                [btn("🏠 Меню", "home")]]}


def fb_filter(first, second, lo=0.0, hi=0.0, pmin=0.0):
    """Фрибетные вилки по выбору пользователя: фрибет на first, противоположные ставки только на second (пусто = на любом другом),
    коэффициент ставки на фрибет в пределах [lo, hi] (0 = без ограничения)."""
    out = []
    with STORE.lock:
        for a in STORE.fball:
            if a["fb_bk"] != first:
                continue
            k = a["stakes"][0][2]
            if k < lo or (hi and k > hi) or a["pct"] < pmin:
                continue
            if second and {bk for _, bk, _, _ in a["stakes"][1:]} != {second}:
                continue
            out.append(a)
    return sorted(out, key=sort_key)


def _rng(u):
    lo, hi = float(u.get("fbmin") or 0), float(u.get("fbmax") or 0)
    if not lo and not hi:
        return "любой коэф."
    return "коэф. %s" % (("%g–%g" % (lo, hi)) if lo and hi else ("от %g" % lo if lo else "до %g" % hi))


def fb_title(u):
    pm = float(u.get("fbpct") or 0)
    return "%s → %s, %s, %sфрибет %s ₽" % (BK_TITLE[u["fb1"]], BK_TITLE[u["fb2"]] if u.get("fb2") else "любой БК", _rng(u),
                                           ("прибыль от %g%%, " % pm) if pm else "", _money(u["fbsum"]))


def show_fb_entry(cfg, chat, mid):
    u = USERS.get(chat) or {}
    V = view(chat)
    V["pending_fb"] = False
    if u.get("fb1") in BKS and u.get("fbsum"):
        show(cfg, chat, mid, "🎁 <b>Фрибетные вилки</b>\nВаш фильтр: <b>%s</b>" % esc(fb_title(u)),
             {"inline_keyboard": [[btn("📋 Показать вилки", "fbgo")], [btn("✏️ Изменить фильтр", "fbedit")],
                                  [btn("🏠 Меню", "home")]]})
    else:
        fb_step1(cfg, chat, mid)


def fb_step1(cfg, chat, mid):
    show(cfg, chat, mid, "🎁 <b>Фрибет · шаг 1 из 5</b>\nНа каком БК у вас фрибет?", kb_fb())


def fb_step2(cfg, chat, mid, first):
    oth = [b for b in BKS if b != first]
    rows = [[btn(BK_TITLE[b], "fb2:%s:%s" % (first, b)) for b in oth[:3]], [btn(BK_TITLE[b], "fb2:%s:%s" % (first, b)) for b in oth[3:]],
            [btn("Любой БК", "fb2:%s:*" % first)], [btn("⬅️ Назад", "fbedit")]]
    show(cfg, chat, mid, "🎁 <b>Фрибет · шаг 2 из 5</b>\nФрибет: <b>%s</b>\nНа каком БК ставить противоположные ставки (деньгами)?" %
         BK_TITLE[first], {"inline_keyboard": rows})


def fb_step3(cfg, chat, mid):
    V = view(chat)
    V["pending_fb"], V["fb_mid"] = 3, mid
    rows = [[btn("Любой", "fbr:0:0"), btn("1.5–3", "fbr:1.5:3"), btn("2–5", "fbr:2:5")],
            [btn("3–10", "fbr:3:10"), btn("от 5", "fbr:5:0"), btn("до 3", "fbr:0:3")], [btn("⬅️ Назад", "fbedit")]]
    show(cfg, chat, mid, "🎁 <b>Фрибет · шаг 3 из 5</b>\nКоэффициент ставки на фрибет: выберите кнопкой или напишите диапазон, "
                         "например <code>2-5</code> (от 2 до 5), <code>от 3</code> или <code>до 4</code>.", {"inline_keyboard": rows})


def fb_step_pct(cfg, chat, mid):
    V = view(chat)
    V["pending_fb"], V["fb_mid"] = 5, mid
    rows = [[btn("Любая", "fbp:0"), btn("от 10%", "fbp:10"), btn("от 20%", "fbp:20"), btn("от 30%", "fbp:30")],
            [btn("от 40%", "fbp:40"), btn("от 50%", "fbp:50"), btn("от 60%", "fbp:60"), btn("от 70%", "fbp:70")],
            [btn("от 80%", "fbp:80"), btn("от 90%", "fbp:90")], [btn("⬅️ Назад", "fbedit")]]
    show(cfg, chat, mid, "🎁 <b>Фрибет · шаг 4 из 5</b>\nМинимальная прибыль (конверсия фрибета): выберите кнопкой или напишите число в %, "
                         "например <code>25</code>. Это доля от суммы фрибета: при фрибете 1000 ₽ и 30% прибыль будет 300 ₽. "
                         "Выше ~90–95% конверсии не бывает.", {"inline_keyboard": rows})


def fb_step4(cfg, chat, mid):
    V = view(chat)
    V["pending_fb"], V["fb_mid"] = 4, mid
    show(cfg, chat, mid, "🎁 <b>Фрибет · шаг 5 из 5</b>\nНапишите сумму фрибета (₽), например <code>2000</code>.",
         {"inline_keyboard": [[btn("⬅️ Назад", "fbedit")]]})


def _parse_range(text):
    t = text.lower().replace(",", ".").replace("—", "-").replace("–", "-")
    nums = [float(x) for x in re.findall(r"\d+(?:\.\d+)?", t)]
    if not nums:
        return None
    if t.strip().startswith("до") and len(nums) == 1:
        return 0.0, nums[0]
    if t.strip().startswith("от") and len(nums) == 1:
        return nums[0], 0.0
    if len(nums) == 1:
        return 0.0, nums[0]                                        # одно число = максимум
    lo, hi = sorted(nums[:2])
    return lo, hi


def _cash_rng(u):
    t = "прибыль от %+g%% до %g%%" % (float(u.get("cmin", 0.0)), float(u.get("cmax", 1000.0)))
    b1, b2 = u.get("cbk1", ""), u.get("cbk2", "")
    if b1:
        t += ", БК: %s + %s" % (BK_TITLE[b1], BK_TITLE[b2] if b2 else "любая")
    elif b2:
        t += ", БК: любая + %s" % BK_TITLE[b2]
    if u.get("ctoday"):
        t += ", только сегодня"
    return t


def cash_pass(u, a, end_today):
    """Подходит ли денежная вилка фильтру пользователя: прибыль, БК (первая и вторая, порядок не важен), «только сегодня»."""
    lo, hi = float(u.get("cmin", 0.0)), float(u.get("cmax", 1000.0))
    if not (lo <= a["pct"] <= hi):
        return False
    bks = {bk for _, bk, _, _ in a["stakes"]}
    for k in (u.get("cbk1", ""), u.get("cbk2", "")):
        if k and k not in bks:
            return False
    if u.get("ctoday") and a["event"]["start"] > end_today:
        return False
    return True


def _parse_signed(text):
    """«-1 1000», «от -1 до 50», «-2--0.5», «0.5» (одно число = минимум) -> (min, max)."""
    t = text.lower().replace(",", ".").replace("—", "-").replace("–", "-").replace("до", " ").replace("от", " ").replace("%", " ")
    m = re.fullmatch(r"\s*(-?\d+(?:\.\d+)?)\s*-\s*(-?\d+(?:\.\d+)?)\s*", t)
    nums = [float(m.group(1)), float(m.group(2))] if m else [float(x) for x in re.findall(r"(?<![\d.])-?\d+(?:\.\d+)?", t)]
    if not nums:
        return None
    if len(nums) == 1:
        return nums[0], 1000.0
    lo, hi = sorted(nums[:2])
    return lo, hi


def cash_filter_screen(cfg, chat, mid):
    V = view(chat)
    V["pending_cash"], V["cash_mid"], V["pending_fb"] = True, mid, False
    u = USERS.get(chat) or {}
    rows = [[btn("🏦 Выбрать БК (первая и вторая)", "cbk")],
            [btn(("✅ " if u.get("ctoday") else "") + "Только сегодня", "ctoday"),
             btn(("✅ " if not u.get("ctoday") else "") + "Все дни", "call")],
            [btn("Только прибыльные (от 0%)", "cr:0:1000")],
            [btn("От 0.5%", "cr:0.5:1000"), btn("От 1%", "cr:1:1000"), btn("От 2%", "cr:2:1000")],
            [btn("От 3%", "cr:3:1000"), btn("От 5%", "cr:5:1000"), btn("От 10%", "cr:10:1000")],
            [btn("С убыточными: от -1%", "cr:-1:1000"), btn("От -3%", "cr:-3:1000")],
            [btn("📋 Показать вилки", "cash")], [btn("🏠 Меню", "home")]]
    show(cfg, chat, mid, "💰 <b>Фильтр денежных вилок</b>\nСейчас: <b>%s</b>\n\nВыберите кнопкой или напишите диапазон прибыли в %%, "
                         "например <code>0.5 5</code> (от 0,5%% до 5%%).\n"
                         "Вилки идут по времени матча: сначала самые ближайшие." % esc(_cash_rng(u)), {"inline_keyboard": rows})


def cash_bk1(cfg, chat, mid):
    rows = [[btn(BK_TITLE[b], "cb1:" + b) for b in BKS[:3]], [btn(BK_TITLE[b], "cb1:" + b) for b in BKS[3:6]], [btn(BK_TITLE[b], "cb1:" + b) for b in BKS[6:]],
            [btn("Любая БК", "cb1:*")], [btn("⬅️ Назад", "cedit")]]
    show(cfg, chat, mid, "💰 <b>Фильтр БК · шаг 1 из 2</b>\nПервая букмекерская контора (нужная вам):", {"inline_keyboard": rows})


def cash_bk2(cfg, chat, mid, first):
    others = [b for b in BKS if b != first]
    rows = [[btn(BK_TITLE[b], "cb2:%s:%s" % (first, b)) for b in others[:3]], [btn(BK_TITLE[b], "cb2:%s:%s" % (first, b)) for b in others[3:6]], [btn(BK_TITLE[b], "cb2:%s:%s" % (first, b)) for b in others[6:]],
            [btn("Любая БК", "cb2:%s:*" % first)], [btn("⬅️ Назад", "cbk")]]
    show(cfg, chat, mid, "💰 <b>Фильтр БК · шаг 2 из 2</b>\nПервая: <b>%s</b>\nВторая букмекерская контора:" %
         (BK_TITLE[first] if first in BK_TITLE else "любая"), {"inline_keyboard": rows})


def fb_open(cfg, chat, mid):
    u = USERS.get(chat) or {}
    V = view(chat)
    V["ids"] = [a["id"] for a in fb_filter(u["fb1"], u.get("fb2", ""), float(u.get("fbmin") or 0), float(u.get("fbmax") or 0), float(u.get("fbpct") or 0))]
    V["pos"], V["title"], V["pending_fb"] = 0, "fb", False
    show_card(cfg, chat, mid)


def kb_card(aid, pos, n):
    return {"inline_keyboard": [[btn("⬅️ Пред.", "prev"), btn("%d / %d" % (pos + 1, n), "noop"), btn("След. ➡️", "next")],
                                [btn("🧮 Рассчитать вилку", "calc:" + aid)], [btn("🏠 Меню", "home")]]}


def settings_view(cfg, u):
    mps = sorted({round(cfg["min_profit"], 2)} | {x for x in (0.5, 1.0, 2.0, 3.0) if x > cfg["min_profit"]})
    cvs = sorted({round(cfg["min_conv"], 1)} | {x for x in (20.0, 30.0, 40.0, 50.0, 70.0, 90.0) if x > cfg["min_conv"]})
    mark = lambda cond, t: ("✓ " if cond else "") + t
    txt = ("⚙️ <b>Настройки</b>\n🔔 Автоотправка новых вилок: %s\n💰 Денежные вилки: %s, от %+g%%\n🎁 Фрибетные вилки: %s%s" % (
        "вкл" if u.get("push") else "выкл (вилки смотрите в меню)",
        "вкл" if u.get("cash", True) else "выкл", u.get("min_profit", cfg["min_profit"]),
        ("вкл, конверсия от %g%%, фрибет на %s" % (u.get("min_conv", 70), BK_IN[u.get("fb_bk", "")]))
        if u.get("fb_auto") else "выкл", ""))
    rows = [[btn(("🔔 Автоотправка: вкл" if u.get("push") else "🔕 Автоотправка: выкл"), "s:push")],
            [btn(("✅ " if u.get("cash", True) else "❌ ") + "Денежные вилки", "s:cash")],
            [btn(mark(abs(u.get("min_profit", 0) - x) < 1e-9, "от %g%%" % x), "s:mp:%g" % x) for x in mps],
            [btn(("✅ " if u.get("fb_auto") else "❌ ") + "Фрибетные вилки", "s:fb")],
            [btn(mark(u.get("fb_bk", "") == k, t), "s:bk:" + k) for k, t in (("", "Любая БК"),) + tuple((b, BK_TITLE[b]) for b in FB_BKS[:3])],
            [btn(mark(u.get("fb_bk", "") == k, t), "s:bk:" + k) for k, t in tuple((b, BK_TITLE[b]) for b in FB_BKS[3:])],
            [btn(mark(abs(u.get("min_conv", 0) - x) < 1e-9, "конв. %g%%" % x), "s:cv:%g" % x) for x in cvs],
            [btn("🏠 Меню", "home")]]
    return txt, {"inline_keyboard": rows}


def show(cfg, chat, mid, text, markup):
    if mid:
        try:
            tg_api(cfg, "editMessageText", {"chat_id": chat, "message_id": mid, "text": text, "parse_mode": "HTML",
                                            "disable_web_page_preview": True, "reply_markup": markup})
            return
        except urllib.error.HTTPError as e:
            if e.code == 400 and b"not modified" in e.read():
                return
        except Exception:
            pass
    tg_send(cfg, text, markup, chat)


def do_refresh(cfg, chat, mid):
    """Кнопка «Обновить данные»: запускает новый цикл парсинга и по окончании открывает ленту заново."""
    V = view(chat)
    if V.get("refreshing"):
        return
    V["refreshing"] = True
    title = V.get("title")

    def work():
        try:
            show(cfg, chat, mid, "⏳ Обновляю данные у букмекеров… обычно 1–3 минуты.", None)
            want = CYC["start"] + 1
            REFRESH.set()
            end = time.time() + 420
            while CYC["done"] < want and time.time() < end:
                time.sleep(1.0)
            if title == "cash":
                open_list(cfg, chat, mid, "cash")
            elif title == "fb" and (USERS.get(chat) or {}).get("fbsum"):
                fb_open(cfg, chat, mid)
            else:
                show_menu(cfg, chat, mid)
        except Exception as e:
            log("обновление:", type(e).__name__, e)
        finally:
            V["refreshing"] = False
    threading.Thread(target=work, daemon=True).start()


def show_menu(cfg, chat, mid):
    show(cfg, chat, mid, "📋 <b>Меню ArbPhone</b>\nВсе виды спорта · Фонбет + Винлайн · прематч\nВыберите тип вилок:", kb_menu(is_admin(cfg, chat)))


def show_card(cfg, chat, mid):
    V = view(chat)
    ids = V["ids"]
    if not ids:
        best = STORE.best
        extra = ""
        if best and V["title"] == "cash":
            extra = "\nБлижайший кандидат: %+.2f%% (%s – %s)" % (best["pct"], best["event"]["home"], best["event"]["away"])
        if V["title"] == "fb":
            u = USERS.get(chat) or {}
            what = "фрибетных вилок (%s, конверсия ≥ %.0f%%)" % (fb_title(u) if u.get("fb1") else "", cfg["min_conv"])
            kb = {"inline_keyboard": [[btn("🔄 Обновить данные", "refresh"), btn("🎛 Фильтр", "fbedit")], [btn("🏠 Меню", "home")]]}
        else:
            u = USERS.get(chat) or {}
            what = "денежных вилок (%s)" % _cash_rng(u)
            kb = {"inline_keyboard": [[btn("🎛 Фильтр", "cedit"), btn("🔄 Обновить данные", "refresh")], [btn("🏠 Меню", "home")]]}
        show(cfg, chat, mid, "Сейчас %s нет.%s" % (what, esc(extra)), kb)
        return
    V["pos"] %= len(ids)
    aid = ids[V["pos"]]
    now = time.time()
    with STORE.lock:
        item = STORE.by_id.get(aid)
    if not item:
        V["ids"] = []
        return show_card(cfg, chat, mid)
    a = item[0]
    V["last"] = aid
    kb = kb_card(aid, V["pos"], len(ids))
    if V["title"] == "cash":
        kb = {"inline_keyboard": kb["inline_keyboard"][:2] + [[btn("🎛 Фильтр", "cedit"), btn("🔄 Обновить", "refresh")],
                                                              [btn("🏠 Меню", "home")]]}
    if V["title"] == "fb":                                      # сумма фрибета уже выбрана: пересчитываем под неё, кнопка «Рассчитать» не нужна
        u = USERS.get(chat) or {}
        if u.get("fbsum"):
            a = dict(a, base_sum=float(u["fbsum"]))
        kb = {"inline_keyboard": [kb["inline_keyboard"][0], [btn("🎛 Фильтр", "fbedit"), btn("🔄 Обновить", "refresh")],
                                  [btn("🏠 Меню", "home")]]}
    show(cfg, chat, mid, render(a, cfg, int(now - a["t_data"]), int(STORE.age(aid, now))), kb)


def open_list(cfg, chat, mid, kind):
    V = view(chat)
    with STORE.lock:
        if kind == "cash":
            u = USERS.get(chat) or {}
            end_today = dt.datetime.now(MSK).replace(hour=23, minute=59, second=59, microsecond=0).timestamp()
            sel = [a for a in STORE.cash if cash_pass(u, a, end_today)]
            plus = sorted((a for a in sel if a["pct"] >= 0), key=lambda a: (a["event"]["start"], -a["pct"]))   # сначала плюсовые: ближайшие по времени матча
            minus = sorted((a for a in sel if a["pct"] < 0), key=lambda a: -a["pct"])   # потом (если включены) минусовые: от меньшего минуса
            lst = plus + minus
        else:
            lst = sorted(STORE.fb[kind], key=sort_key)
        V["ids"] = [a["id"] for a in lst]
    V["pos"], V["title"] = 0, ("cash" if kind == "cash" else "fb")
    show_card(cfg, chat, mid)


def ask_amount(cfg, chat, aid, mid=None, markup=None):
    with STORE.lock:
        item = STORE.by_id.get(aid)
    if not item:
        return tg_send(cfg, "Вилка уже не в списке. Откройте меню и выберите заново.", None, chat)
    a, V = item[0], view(chat)
    V["pending"], V["last"] = aid, aid
    V["calc_mid"], V["calc_markup"] = mid, markup               # сообщение с вилкой, под которым покажем расчёт
    if a["mode"] == "cash":
        q = "Сумма ставки (₽) на первом букмекере: <b>%s</b>" % BK_TITLE[a["stakes"][0][1]]
    else:
        q = "Размер фрибета (₽) на <b>%s</b>" % BK_TITLE[a["stakes"][0][1]]
    try:
        r = tg_api(cfg, "sendMessage", {"chat_id": chat, "text": "🧮 " + q, "parse_mode": "HTML"})
        V["prompt_mid"] = r["result"]["message_id"]
    except Exception:
        V["prompt_mid"] = None


def _del(cfg, chat, mid):
    if mid:
        try:
            tg_api(cfg, "deleteMessage", {"chat_id": chat, "message_id": mid})
        except Exception:
            pass


def do_calc(cfg, chat, text, user_mid=None):
    V = view(chat)
    aid = V["pending"] or V["last"]
    try:
        amount = float(text.replace(" ", "").replace(",", "."))
    except ValueError:
        return False
    if amount <= 0 or amount > 1e8:
        return False
    with STORE.lock:
        item = STORE.by_id.get(aid) if aid else None
    if not item:
        tg_send(cfg, "Сначала откройте вилку в меню и нажмите «Рассчитать».", {"inline_keyboard": [[btn("🏠 Меню", "home")]]}, chat)
        return True
    a, seen = item
    now = time.time()
    full = render(a, cfg, int(now - a["t_data"]), int(STORE.age(a["id"], now))) + "\n\n" + render_calc(a, amount, now - seen, cfg)
    markup = V.get("calc_markup") or {"inline_keyboard": [[btn("🧮 Другая сумма", "calc:" + a["id"])], [btn("🏠 Меню", "home")]]}
    mid, done = V.get("calc_mid") if V["pending"] else None, False
    if mid:                                                     # дописываем расчёт под той же вилкой
        try:
            tg_api(cfg, "editMessageText", {"chat_id": chat, "message_id": mid, "text": full, "parse_mode": "HTML",
                                            "disable_web_page_preview": True, "reply_markup": markup})
            done = True
        except Exception:
            done = False
    if not done:
        tg_send(cfg, full, markup, chat)
    _del(cfg, chat, V.get("prompt_mid"))                        # убираем вопрос и введённое число, чтобы чат не засорялся
    _del(cfg, chat, user_mid)
    V["pending"], V["prompt_mid"] = None, None
    return True


def show_status(cfg, chat, mid):
    with STORE.lock:
        ago = int(time.time() - STORE.updated) if STORE.updated else -1
        txt = "📊 <b>Статус</b> (%s)\n%s\nПоследний цикл: %s\nДенежных вилок: %d\nФрибетных: %s" % (
            esc(cfg["node"]), esc(STORE.info), ("%d с назад" % ago) if ago >= 0 else "нет",
            len(STORE.cash), ", ".join("%s %d" % (BK_TITLE[b], len(STORE.fb[b])) for b in BKS))
    if str(chat) == str(cfg["chat_id"]):
        txt += "\nПодписчиков: %d" % len(USERS.active())
    show(cfg, chat, mid, txt, {"inline_keyboard": [[btn("🏠 Меню", "home")]]})


def show_settings(cfg, chat, mid):
    u = USERS.get(chat) or {}
    txt, kb = settings_view(cfg, u)
    show(cfg, chat, mid, txt, kb)


def on_setting(cfg, chat, mid, data):
    u = USERS.get(chat) or {}
    parts = data.split(":")
    if parts[1] == "push":
        USERS.set(chat, push=not u.get("push"))
    elif parts[1] == "cash":
        USERS.set(chat, cash=not u.get("cash", True))
    elif parts[1] == "fb":
        USERS.set(chat, fb_auto=not u.get("fb_auto"))
    elif parts[1] == "mp":
        USERS.set(chat, min_profit=max(float(parts[2]), cfg["min_profit"]))
    elif parts[1] == "cv":
        USERS.set(chat, min_conv=max(float(parts[2]), cfg["min_conv"]))
    elif parts[1] == "bk" and parts[2] in ("",) + BKS:
        USERS.set(chat, fb_bk=parts[2])
    show_settings(cfg, chat, mid)


def on_callback(cfg, cq):
    data, msg = cq.get("data", ""), cq.get("message") or {}
    chat, mid = (msg.get("chat") or {}).get("id"), msg.get("message_id")
    try:
        tg_api(cfg, "answerCallbackQuery", {"callback_query_id": cq["id"]})
    except Exception:
        pass
    V = view(chat)
    if admin_callback(cfg, chat, mid, data):
        return
    if data not in ("cedit", "ctoday", "call"):
        V["pending_cash"] = False
    if data == "home":
        show_menu(cfg, chat, mid)
    elif data == "cash":
        V["pending_cash"] = False
        open_list(cfg, chat, mid, "cash")
    elif data == "fb":
        show_fb_entry(cfg, chat, mid)
    elif data == "refresh":
        do_refresh(cfg, chat, mid)
    elif data == "cedit":
        cash_filter_screen(cfg, chat, mid)
    elif data == "cbk":
        cash_bk1(cfg, chat, mid)
    elif data.startswith("cb1:") and (data[4:] in BKS or data[4:] == "*"):
        cash_bk2(cfg, chat, mid, data[4:])
    elif data.startswith("cb2:"):
        try:
            _, f, sec = data.split(":")
        except ValueError:
            return
        f, sec = ("" if f == "*" else f), ("" if sec == "*" else sec)
        if (f and f not in BKS) or (sec and sec not in BKS):
            return
        if not f and sec:
            f, sec = sec, ""
        USERS.set(chat, cbk1=f, cbk2=sec)
        open_list(cfg, chat, mid, "cash")
    elif data in ("ctoday", "call"):
        USERS.set(chat, ctoday=(data == "ctoday"))
        cash_filter_screen(cfg, chat, mid)
    elif data.startswith("cr:"):
        try:
            _, lo, hi = data.split(":")
            USERS.set(chat, cmin=float(lo), cmax=float(hi))
        except ValueError:
            return
        V["pending_cash"] = False
        open_list(cfg, chat, mid, "cash")
    elif data == "fbedit":
        V["pending_fb"] = False
        fb_step1(cfg, chat, mid)
    elif data.startswith("fb1:") and data[4:] in BKS:
        fb_step2(cfg, chat, mid, data[4:])
    elif data.startswith("fb2:"):
        _, first, second = (data.split(":") + ["", ""])[:3]
        if first in BKS and (second in BKS or second == "*"):
            USERS.set(chat, fb1=first, fb2="" if second == "*" else second)
            fb_step3(cfg, chat, mid)
    elif data.startswith("fbr:"):
        try:
            _, lo, hi = data.split(":")
            USERS.set(chat, fbmin=float(lo), fbmax=float(hi))
        except ValueError:
            return
        fb_step_pct(cfg, chat, mid)
    elif data.startswith("fbp:"):
        try:
            USERS.set(chat, fbpct=max(0.0, float(data[4:])))
        except ValueError:
            return
        fb_step4(cfg, chat, mid)
    elif data == "fbgo":
        u = USERS.get(chat) or {}
        if u.get("fb1") in BKS and u.get("fbsum"):
            fb_open(cfg, chat, mid)
        else:
            fb_step1(cfg, chat, mid)
    elif data == "next":
        V["pos"] += 1
        show_card(cfg, chat, mid)
    elif data == "prev":
        V["pos"] -= 1
        show_card(cfg, chat, mid)
    elif data == "stat":
        show_status(cfg, chat, mid)
    elif data == "set":
        show_settings(cfg, chat, mid)
    elif data.startswith("s:"):
        on_setting(cfg, chat, mid, data)
    elif data.startswith("calc:"):
        ask_amount(cfg, chat, data[5:], mid, msg.get("reply_markup"))


def _fb_sum(cfg, chat, text, user_mid):
    """Текст в мастере фрибета: на шаге 3 — диапазон коэффициента, на шаге 4 — сумма фрибета."""
    V = view(chat)
    step = V.get("pending_fb")
    if step == 3:
        r = _parse_range(text)
        if not r:
            return False
        USERS.set(chat, fbmin=r[0], fbmax=r[1])
        _del(cfg, chat, user_mid)
        fb_step_pct(cfg, chat, V.get("fb_mid"))
        return True
    if step == 5:
        try:
            pm = float(text.replace("%", "").replace(",", ".").strip())
        except ValueError:
            return False
        if not 0 <= pm < 1000:
            return False
        USERS.set(chat, fbpct=pm)
        _del(cfg, chat, user_mid)
        fb_step4(cfg, chat, V.get("fb_mid"))
        return True
    try:
        amount = float(text.replace(" ", "").replace(",", "."))
    except ValueError:
        return False
    if amount <= 0 or amount > 1e8:
        return False
    USERS.set(chat, fbsum=amount)
    _del(cfg, chat, user_mid)
    fb_open(cfg, chat, V.get("fb_mid"))
    return True


_BLOCK_NOTE = {}
_WARM = {}
WARM_URL = {"ligastavok": "https://www.ligastavok.ru/", "olimp": "https://www.olimp.bet/", "betcity": "https://betcity.ru/", "betboom": "https://betboom.ru/"}


def warm_up(cfg, bk):
    """Автопрогрев: открыть сайт БК в браузере телефона (termux-open-url), подождать и сбросить паузу этой БК.
    Не чаще раза в warmup_every секунд на БК. -> True, если прогрев запущен."""
    if not cfg.get("auto_warmup", True) or bk not in WARM_URL or not shutil.which("termux-open-url"):
        return False
    if time.time() - _WARM.get(bk, 0) < float(cfg.get("warmup_every", 1800)):
        return False
    _WARM[bk] = time.time()

    def run():
        try:
            subprocess.run(["termux-open-url", WARM_URL[bk]], timeout=20, capture_output=True)
            log("прогрев: открыл %s в браузере, жду %d с" % (WARM_URL[bk], int(cfg.get("warmup_wait", 40))))
            time.sleep(float(cfg.get("warmup_wait", 40)))
            log("прогрев: паузы сброшены: %s" % (", ".join(retry_connections(only=bk)) or "нечего сбрасывать"))
        except Exception as e:
            log("прогрев %s не удался: %s" % (bk, e))
    threading.Thread(target=run, daemon=True).start()
    return True


def notify_block(cfg, bk, name):
    """Блокировка БК: автопрогрев в браузере телефона и сообщение в Telegram (не чаще раза в 3 часа на БК)."""
    warmed = warm_up(cfg, bk)
    if time.time() - _BLOCK_NOTE.get(bk, 0) < 3 * 3600:
        return
    _BLOCK_NOTE[bk] = time.time()
    try:
        if warmed:
            tg_send(cfg, "⚠️ %s закрыл доступ с адреса телефона (блокировка). Я сам открыл сайт в браузере телефона (прогрев) и через "
                         "~%d с попробую снова. Если не поможет — откройте сайт %s в Chrome, перезагрузите страницу и напишите /retry."
                    % (name, int(cfg.get("warmup_wait", 40)), name))
        else:
            tg_send(cfg, "⚠️ %s закрыл доступ с адреса телефона (блокировка). Что сделать: откройте сайт %s в Chrome на телефоне, "
                         "подождите несколько секунд, перезагрузите страницу и напишите боту /retry. Остальные БК работают." % (name, name))
    except Exception:
        pass


RETRY_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "retry_now")


def retry_connections(only=None):
    """Сбросить паузы после блокировок (Олимп, Бетсити, Лига Ставок): ближайший цикл попробует подключиться сразу.
    Ведро запросов не сбрасываем целиком: первый запрос разрешён сразу, дальше — как обычно. -> список затронутых БК."""
    now, done = time.time(), []
    with OL_LOCK:
        if OL_CACHE["pause"] > now and only in (None, "olimp"):
            OL_CACHE["pause"] = 0.0
            OL_RATE["tok"], OL_RATE["tok_t"] = 0.0, now
            done.append("Олимп")
    with BC_LOCK:
        if (BC_CACHE.get("pause", 0) > now or BC_CACHE.get("dpause", 0) > now) and only in (None, "betcity"):
            BC_CACHE["pause"] = BC_CACHE["dpause"] = 0.0
            BC_RATE["tok"], BC_RATE["tok_t"] = 0.0, now
            done.append("Бетсити")
    if LS_CACHE.get("pause", 0) > now and only in (None, "ligastavok"):
        LS_CACHE["pause"] = 0.0
        done.append("Лига Ставок")
    return done


def on_message(cfg, m, admin):
    chat, text = m["chat"]["id"], (m.get("text") or "").strip()
    low = text.lower().split("@")[0]
    if low in ("/start", "/menu", "меню") or low.startswith("/start "):
        show_menu(cfg, chat, None)
    elif low == "/settings":
        show_settings(cfg, chat, None)
    elif low == "/stop":
        USERS.set(chat, active=False)
        tg_send(cfg, "Вы отписаны от вилок. Чтобы вернуться, напишите /start.", None, chat)
    elif low == "/retry" and admin:
        done = retry_connections()
        tg_send(cfg, ("🔄 Паузы сброшены: %s. Ближайший цикл (1–3 мин) попробует подключиться сразу." % ", ".join(done)) if done
                else "Сейчас ни одна БК не стоит на паузе после блокировки.", None, chat)
    elif low.startswith("/grant") and admin:
        a = text.split()
        try:
            target, days = a[1], int(a[2])
            if sub_grant(cfg, target, days) is None:
                tg_send(cfg, "Пользователь %s не найден: он должен сначала написать боту /start." % esc(target), None, chat)
            else:
                tg_send(cfg, "✅ Доступ выдан: %s, +%d дн." % (esc(target), days), None, chat)
        except (IndexError, ValueError):
            tg_send(cfg, "Формат: /grant ID ДНИ, например <code>/grant 123456789 30</code>", None, chat)
    elif low.startswith("/revoke") and admin:
        a = text.split()
        if len(a) > 1 and USERS.get(a[1]) is not None:
            sub_revoke(cfg, a[1])
            tg_send(cfg, "Доступ отключён: %s" % esc(a[1]), None, chat)
        else:
            tg_send(cfg, "Формат: /revoke ID", None, chat)
    elif low == "/id":
        tg_send(cfg, "Ваш chat id: <code>%s</code>%s" % (chat, " (вы владелец бота)" if admin else ""), None, chat)
    elif low.startswith("/promo_new") and admin:
        a = text.split()
        try:
            days, uses = int(a[1]), int(a[2]) if len(a) > 2 else 1
            code = PROMOS.create(days, uses)
            tg_send(cfg, "🎟 Новый промокод: <code>%s</code>\n%d дн., активаций: %d" % (fmt_promo(code), days, uses), None, chat)
        except (IndexError, ValueError):
            tg_send(cfg, "Формат: <code>/promo_new ДНИ ЧИСЛО_АКТИВАЦИЙ</code>, например <code>/promo_new 30 5</code>", None, chat)
    elif low.startswith("/promo"):
        a = text.split(None, 1)
        if len(a) > 1:
            promo_redeem(cfg, chat, a[1])
        else:
            view(chat)["pending_promo"] = True
            tg_send(cfg, "🎟 Отправьте промокод одним сообщением.", None, chat)
    elif view(chat).get("pending_promo") and not text.startswith("/"):
        view(chat)["pending_promo"] = False
        promo_redeem(cfg, chat, text)
    elif low in ("/admin", "админ", "админка") and admin:
        show_admin(cfg, chat, None)
    elif low == "/users" and admin:
        act = USERS.active()
        tg_send(cfg, "👥 Подписчиков: %d\n%s" % (len(act), "\n".join(
            "%s (%s)" % (esc(u.get("name", "")), c) for c, u in act[:40])), None, chat)
    elif view(chat).get("pending_cash") and _parse_signed(text):
        lo, hi = _parse_signed(text)
        USERS.set(chat, cmin=lo, cmax=hi)
        view(chat)["pending_cash"] = False
        _del(cfg, chat, m.get("message_id"))
        open_list(cfg, chat, view(chat).get("cash_mid"), "cash")
    elif view(chat).get("pending_fb") and _fb_sum(cfg, chat, text, m.get("message_id")):
        pass
    elif not do_calc(cfg, chat, text, m.get("message_id")):
        tg_send(cfg, "Откройте /menu. Чтобы посчитать ставки, нажмите «Рассчитать» под вилкой и введите сумму.", None, chat)


def handle_update(cfg, u):
    obj = u.get("callback_query") or u.get("message")
    if not obj:
        return
    chat = ((obj.get("message") or obj).get("chat") or {}).get("id")
    if not cfg["chat_id"]:
        return tg_send(cfg, "Ваш chat id: %s — впишите его в ARB_CHAT_ID." % chat, None, chat)
    admin = str(chat) == str(cfg["chat_id"])
    user = USERS.get(chat)
    if admin and not (user and user.get("active")) and "message" in u:
        pass                                        # владельца пускаем всегда
    if not admin and not (user and user.get("active")):
        text = ((u.get("message") or {}).get("text") or "").strip()
        parts = text.split()
        if "message" in u and parts and parts[0].lower().split("@")[0] == "/start":
            code = parts[1] if len(parts) > 1 else ""
            if cfg["open_access"] and (not cfg["invite_code"] or code == cfg["invite_code"]):
                frm = u["message"].get("from") or {}
                name = frm.get("username") and "@" + frm["username"] or frm.get("first_name") or str(chat)
                if USERS.add(cfg, chat, name):
                    tg_send(cfg, "👤 Новый подписчик: %s (%s)" % (esc(name), chat))
                show_menu(cfg, chat, None)
            else:
                tg_send(cfg, "🔒 Доступ закрыт. Если у вас есть код приглашения, напишите: /start КОД", None, chat)
        elif "callback_query" in u:
            try:
                tg_api(cfg, "answerCallbackQuery", {"callback_query_id": u["callback_query"]["id"], "text": "Напишите /start"})
            except Exception:
                pass
        else:
            tg_send(cfg, "Напишите /start, чтобы получать вилки.", None, chat)
        return
    if admin and not user:
        USERS.add(cfg, chat, "владелец")
    if "callback_query" in u:
        on_callback(cfg, u["callback_query"])
    else:
        on_message(cfg, u["message"], admin)


def bot_loop(cfg):
    offset, warned = 0, False
    while True:
        try:
            r = tg_api(cfg, "getUpdates", {"offset": offset, "timeout": 25,
                                           "allowed_updates": ["message", "callback_query"]}, timeout=40)
            warned = False
            for u in r.get("result", []):
                offset = u["update_id"] + 1
                try:
                    handle_update(cfg, u)
                except Exception as e:
                    log("меню:", type(e).__name__, e)
        except urllib.error.HTTPError as e:
            if not warned:
                log("меню getUpdates HTTP", e.code, "(409 = второй экземпляр бота с этим токеном)")
                warned = True
            time.sleep(10)
        except Exception as e:
            time.sleep(5)


# ============================================================ диагностика

def qc(pairs, tag=""):
    errs = collections.defaultdict(list)
    for w, f, sw in pairs:
        fm = _flip(f["markets"]) if sw else f["markets"]
        for key, wd in w["markets"].items():
            fd = fm.get(key)
            if fd and set(fd) == set(wd):
                errs[key.rsplit(":", 1)[0] if ":" in key else key].append(sum(abs(math.log(wd[o] / fd[o])) for o in wd) / len(wd))
    for k, v in errs.items():
        v.sort()
        log("QC %s%-5s n=%4d медиана|ln|=%.3f  доля>0.20: %.1f%%" %
            (tag + " " if tag else "", k, len(v), v[len(v) // 2], 100.0 * sum(x > 0.2 for x in v) / len(v)))


# ============================================================ цикл

def show_compare(pairs, name):
    """--show Гавр: печатает коэффициенты Винлайна и Фонбета рядом — для сверки с приложениями."""
    q = name.lower().replace("ё", "е")
    for w, f, sw in pairs:
        if q not in (w["home"] + " " + w["away"] + " " + f["home"] + " " + f["away"]).lower().replace("ё", "е"):
            continue
        fm = _flip(f["markets"]) if sw else f["markets"]
        print("\n%s – %s  |  %s  | %s" % (w["home"], w["away"], f["league"],
                                         dt.datetime.fromtimestamp(w["start"], MSK).strftime("%d.%m %H:%M МСК")))
        print("%-12s %-22s %-22s" % ("рынок", "Фонбет", "Винлайн"))
        def _ord(k):
            tail = k.rsplit(":", 1)[-1]
            try:
                return (k.rsplit(":", 1)[0], float(tail))
            except ValueError:
                return (k, 0.0)
        keys = sorted(set(w["markets"]) | set(fm), key=_ord)
        for k in keys:
            fmt = lambda d: " / ".join("%s %.2f" % (o, v) for o, v in d.items()) if d else "—"
            print("%-12s %-22s %-22s" % (k, fmt(fm.get(k)), fmt(w["markets"].get(k))))


def load_har(args):
    with open(args.har_fonbet, encoding="utf-8") as fh:
        fe = json.load(fh)["log"]["entries"][0]
    doc = json.loads(fe["response"]["content"]["text"])
    with open(args.har_winline, encoding="utf-8") as fh:
        ws = json.load(fh)["log"]["entries"][0]["_webSocketMessages"]
    msgs = [x for x in (_gunzip(base64.b64decode(m["data"])) for m in ws
                        if m["type"] == "receive" and m["opcode"] == 2) if x]
    return doc, msgs


def add_corners(cfg, pairs):
    """Угловые Винлайна лежат только на странице матча: для ближайших матчей, где угловые есть у Фонбета, запрашиваем её."""
    cand = [p for p in pairs if p[0].get("wid") and any(k.startswith(("CRN:", "1H:CRN:")) for k in p[1]["markets"])]
    cand.sort(key=lambda p: p[0]["start"])
    cand = cand[:cfg["corners_max"]]
    if not cand:
        return
    try:
        det = winline_details(cfg, [p[0]["wid"] for p in cand])
    except SystemExit:
        raise
    except Exception as e:
        log("угловые Винлайна недоступны: %s: %s" % (type(e).__name__, e))
        return
    n = 0
    for w, f, sw in cand:
        cm = corner_markets(det.get(w["wid"]) or [])
        if cm:
            w["markets"].update(cm)
            n += 1
    log("угловые: запрошено %d матчей, получено %d" % (len(cand), n))


def run_cycle(cfg, args, sent):
    offline = bool(args.har_fonbet and args.har_winline)
    if os.path.exists(RETRY_FILE):                              # файл retry_now рядом со скриптом (touch retry_now) = то же, что /retry
        try:
            os.remove(RETRY_FILE)
        except OSError:
            pass
        log("retry_now: паузы сброшены: %s" % (", ".join(retry_connections()) or "нечего сбрасывать"))
    bb, bb_names, t_b = [], {}, None
    bc, t_c = [], None
    lo, t_l = [], None
    ls, t_s = [], None
    ol, t_o = [], None
    ow, t_w1 = [], None
    ma, t_ma = [], None
    pm, t_p = [], None
    fon_r, t_fr, win_r, t_wr = [], None, [], None
    doc = msgs = None
    REM = set(cfg.get("remote_bks") or [])
    if cfg.get("auto_remote", True) and not offline and cfg.get("web_repo") and cfg.get("web_token"):
        try:                                                   # БК, по которым у работников есть свежие данные, главный телефон сам не опрашивает
            remote_load(cfg)
            REM |= {b for b in CL_BKS if remote_events(cfg, b)[0]}
        except SystemExit:
            raise
        except Exception as e:
            log("работники: %s: %s" % (type(e).__name__, e))
    if cfg.get("polymarket") and "polymarket" not in REM and not offline:
        try:
            pm = polymarket_fetch(cfg)
            t_p = PM_CACHE["t"] or None
        except SystemExit:
            raise
        except Exception as e:
            log("Polymarket недоступен: %s: %s" % (type(e).__name__, e))
    if cfg.get("onewin") and "onewin" not in REM and not offline:
        try:
            ow = onewin_fetch(cfg)
            t_w1 = OW_CACHE["t"] or None
        except SystemExit:
            raise
        except Exception as e:
            log("1win недоступен: %s: %s" % (type(e).__name__, e))
    if cfg.get("marathon") and "marathon" not in REM and not offline:
        try:
            ma = marathon_fetch(cfg)
            t_ma = MA_CACHE["t"] or None
        except SystemExit:
            raise
        except Exception as e:
            log("Марафон недоступен: %s: %s" % (type(e).__name__, e))
    if cfg["olimp"] and "olimp" not in REM and not offline:
        try:
            ol = olimp_fetch(cfg)
            t_o = OL_CACHE["t"] or None
        except SystemExit:
            raise
        except Exception as e:
            log("Олимп недоступен: %s: %s" % (type(e).__name__, e))
    if cfg["ligastavok"] and "ligastavok" not in REM and not offline:
        try:
            ls = ls_events(ls_fetch(cfg))
            t_s = LS_CACHE["t"] or None
        except SystemExit:
            raise
        except Exception as e:
            log("Лига Ставок недоступна: %s: %s" % (type(e).__name__, e))
    if cfg["leon"] and "leon" not in REM and not offline:
        try:
            if time.time() < LEON_CACHE.get("pause", 0):
                lo, t_l = [], None
            elif LEON_CACHE["ev"] and time.time() - LEON_CACHE["t"] <= cfg["leon_ttl"]:
                lo, t_l = LEON_CACHE["ev"], LEON_CACHE["t"]
            else:
                lo = leon_events(leon_fetch(cfg))
                t_l = LEON_CACHE["t"] = time.time()
                LEON_CACHE["ev"] = lo
        except SystemExit:
            raise
        except Exception as e:
            log("Леон недоступен: %s: %s" % (type(e).__name__, e))
    if cfg["betcity"] and "betcity" not in REM and not offline:
        try:
            bc = betcity_events(betcity_fetch(cfg))            # догружает только устаревшие пачки; при блокировке отдаёт накопленное
            t_c = BC_CACHE["t"] or None
        except SystemExit:
            raise
        except Exception as e:
            log("Бетсити недоступен: %s: %s" % (type(e).__name__, e))
    if cfg["betboom"] and "betboom" not in REM and not offline:                         # самый долгий запрос — первым, чтобы снимки были свежее
        try:
            bmsgs, bb_names = betboom_fetch(cfg)
            bb = bb_events(bmsgs, bb_names, now=time.time())
            t_b = time.time()
        except SystemExit:
            raise
        except Exception as e:
            log("БетБум недоступен: %s: %s" % (type(e).__name__, e))
    if REM and not offline:                                    # БК, которые опрашивают телефоны-работники
        if not cfg.get("auto_remote", True):
            try:
                remote_load(cfg)
            except SystemExit:
                raise
            except Exception as e:
                log("работники: %s: %s" % (type(e).__name__, e))
        for _bk in REM:
            _ev, _t = remote_events(cfg, _bk)
            if not _ev:
                log("работники: нет свежих данных по %s" % _bk)
            if _bk == "polymarket":
                pm, t_p = _ev, _t
            elif _bk == "onewin":
                ow, t_w1 = _ev, _t
            elif _bk == "marathon":
                ma, t_ma = _ev, _t
            elif _bk == "olimp":
                ol, t_o = _ev, _t
            elif _bk == "ligastavok":
                ls, t_s = _ev, _t
            elif _bk == "leon":
                lo, t_l = _ev, _t
            elif _bk == "betcity":
                bc, t_c = _ev, _t
            elif _bk == "betboom":
                bb, t_b = _ev, _t
            elif _bk == "fonbet":
                fon_r, t_fr = _ev, _t
            elif _bk == "winline":
                win_r, t_wr = _ev, _t
    if offline:
        doc, msgs = load_har(args)
        t_f = t_w = time.time()
        if cfg["betboom"] and args.har_betboom:
            bb, t_b = bb_events(load_bb_har(args.har_betboom)), time.time()
        if cfg["ligastavok"] and args.har_ls:
            raw, pages = load_ls_har(args.har_ls)
            ls, t_s = ls_events(raw, now=args.bc_now or time.time()), time.time()
            for w in ls:
                if w["bid"] in pages:
                    w["markets"].update(ls_markets(pages[w["bid"]], w["sk"]))
        if cfg["olimp"] and args.har_olimp:
            lists, pages = load_olimp_har(args.har_olimp)
            ol, seen_o = [], set()
            for j in lists:
                for w in olimp_parse(j, now=args.bc_now or time.time()):
                    if w["bid"] not in seen_o:
                        seen_o.add(w["bid"])
                        ol.append(w)
            t_o = time.time()
            for w in ol:
                if w["bid"] in pages:
                    w["markets"].update(olimp_markets(pages[w["bid"]], w["sk"]))
        if cfg["leon"] and args.har_leon:
            raw, pages = load_leon_har(args.har_leon)
            lo, t_l = leon_events(raw, now=args.bc_now or time.time()), time.time()
            for w in lo:
                if w["bid"] in pages:
                    w["markets"].update(leon_markets(pages[w["bid"]], w["sk"]))
        if cfg["betcity"] and args.har_betcity:
            evs, exts = load_bc_har(args.har_betcity)
            bc, t_c = betcity_events(evs, now=args.bc_now or time.time()), time.time()
            for u, r in exts:
                m = re.search(r"ids=(\d+)", u)
                for w in bc:
                    if m and int(m.group(1)) == w["bid"]:
                        w["markets"].update(bc_ext_markets(r, w["bid"], "", football=(w["sk"] == "football")))
                    elif m and int(m.group(1)) == (w.get("kid") or 0):
                        w["markets"].update(bc_ext_markets(r, w["kid"], "CRN:"))
    else:
        if fon_r:                                               # Фонбет опрашивает телефон-работник
            t_f = t_fr
        else:
            doc = fonbet_fetch(cfg)
            t_f = time.time()
        if win_r:                                               # Винлайн опрашивает телефон-работник
            t_w = t_wr
        else:
            msgs = winline_fetch(cfg)
            t_w = time.time()
        if not fon_r and not win_r and abs(t_w - t_f) > cfg["max_age"]:
            log("снимки БК слишком разнесены по времени — пропускаю цикл")
            return
        if fon_r or win_r:
            log("Фонбет: %s, Винлайн: %s" % (("от работника, %d с назад" % (time.time() - t_f)) if fon_r else "на этом телефоне",
                                             ("от работника, %d с назад" % (time.time() - t_w)) if win_r else "на этом телефоне"))
        if t_b is not None and t_f - t_b > cfg["max_age"]:
            log("БетБум: снимок устарел на %d с — не использую в этом цикле" % (t_f - t_b))
            bb, t_b = [], None
    fon = fon_r if doc is None else fonbet_parse(doc)
    win = win_r if msgs is None else winline_events(msgs)
    if cfg.get("horizon_hours"):                              # только ближайшие матчи — у всех БК
        lim = (args.bc_now or time.time()) + cfg["horizon_hours"] * 3600
        fon, win, bb, bc, lo, ls, ol, pm, ow, ma = ([x for x in lst if x.get("start", 0) <= lim] for lst in (fon, win, bb, bc, lo, ls, ol, pm, ow, ma))
    pairs = match_events(win, fon)
    pairs_bb = match_events(bb, [x for x in fon if x.get("sk") == "football"])
    pairs_bc = match_events(bc, fon)
    pairs_lo = match_events(lo, fon)
    pairs_ls = match_events(ls, fon)
    pairs_ol = match_events(ol, fon)
    pairs_pm = match_events_pm(pm, fon)
    pairs_ow = match_events(ow, fon)
    pairs_ma = match_events(ma, fon)
    if pairs_ol and not offline:
        add_olimp_details(cfg, pairs_ol)
    if pairs_ls and not offline:
        add_ls_details(cfg, pairs_ls)
    if pairs_lo and not offline:
        add_leon_details(cfg, pairs_lo)
        t_l = LEON_CACHE["t"] = time.time()
    if pairs_bc and not offline:
        add_bc_details(cfg, pairs_bc)
    if cfg["corners"] and not offline:
        add_corners(cfg, pairs)
        t_w = time.time()
    if pairs_bb and not offline:
        add_bb_details(cfg, pairs_bb)
        t_b = time.time()
    if args.show:
        show_compare(pairs, args.show)
    groups = {}
    for bk, prs in (("winline", pairs), ("betboom", pairs_bb), ("betcity", pairs_bc), ("leon", pairs_lo), ("ligastavok", pairs_ls), ("olimp", pairs_ol), ("polymarket", pairs_pm), ("onewin", pairs_ow), ("marathon", pairs_ma)):
        for w, f, sw in prs:
            g = groups.setdefault(f["id"], {"f": f, "mk": {"fonbet": f["markets"]}})
            if bk == "polymarket":
                f["pm"] = (w["away"], w["home"]) if sw else (w["home"], w["away"])      # английские названия в ориентации Фонбета
            g["mk"][bk] = _flip(w["markets"]) if sw else w["markets"]
    cands = find_arbs(list(groups.values()), cfg)
    now = time.time()
    t_data = min(t for t in (t_f, t_w, t_b, t_c, t_l, t_s, t_o, t_p, t_w1, t_ma) if t)
    cash_c = [a for a in cands if a["mode"] == "cash"]
    good = [a for a in cands if acceptable(a, cfg) and (
        a["mode"] == "cash" or (cfg["freebet_auto"] and a["pct"] >= cfg["min_conv_push"] and
                                cfg["freebet_bk"] in ("", a["fb_bk"])))]
    good.sort(key=sort_key)                                   # сначала 2 исхода, потом 3; внутри — по времени матча
    acc = sorted((a for a in cands if acceptable(a, cfg)), key=sort_key)
    sus = sum(1 for a in cash_c if a["div"] > cfg["max_diverge"] and a["pct"] >= cfg["min_profit"])
    info = "Фонбет %d, Винлайн %d, БетБум %d, Бетсити %d, Леон %d, Лига Ставок %d, Олимп %d, Polymarket %d, 1win %d, Марафон %d матчей, совпало %d / %d / %d / %d / %d / %d / %d / %d / %d, рынков %d" % (
        len(fon), len(win), len(bb), len(bc), len(lo), len(ls), len(ol), len(pm), len(ow), len(ma), len(pairs), len(pairs_bb), len(pairs_bc), len(pairs_lo), len(pairs_ls),
        len(pairs_ol), len(pairs_pm), len(pairs_ow), len(pairs_ma), len(cash_c))
    STORE.update(cands, cfg, now, t_data, info)
    if not offline:
        try:
            sub_notices(cfg)
        except Exception as e:
            log("подписки:", type(e).__name__, e)
    if cfg.get("web_repo") and not offline:
        web_publish(cfg, web_payload([a for a in cands if a["mode"] == "cash" or acceptable(a, cfg)], cfg, now, t_data, info))
    log("%s, вилок %d (подозрительных отброшено %d)" % (info, len(good), sus))
    if args.qc:
        qc(pairs, "Винлайн")
        qc(pairs_bb, "БетБум")
        qc(pairs_bc, "Бетсити")
        qc(pairs_lo, "Леон")
        qc(pairs_ls, "Лига Ставок")
        qc(pairs_ol, "Олимп")
        qc(pairs_pm, "Polymarket")
        qc(pairs_ow, "1win")
        qc(pairs_ma, "Марафон")
    for a in cash_c[:args.near]:
        log("  кандидат %+.2f%% %s – %s %s div=%.2f%s" % (a["pct"], a["event"]["home"], a["event"]["away"], a["key"],
                                                         a["div"], " (отброшен)" if not acceptable(a, cfg) else ""))
    for k in [k for k, (t, _) in sent.items() if now - t > cfg["dedup_ttl"]]:
        del sent[k]
    if args.no_send or not cfg["bot_token"]:                   # печать в консоль, как раньше
        for a in good[:cfg["max_msgs"]]:
            print("\n" + re.sub(r"</?[a-z]+[^>]*>", "", render(a, cfg, int(now - t_data), int(STORE.age(a["id"], now)))) + "\n")
        return
    users = USERS.active()
    per_user = collections.Counter()
    delivered = 0
    for a in acc:
        text = None
        for chat, u in users:
            if not u.get("push") or not wants(u, a) or per_user[chat] >= cfg["max_msgs"]:     # автоотправка — только тем, кто её включил
                continue
            k = (chat, a["id"])
            if k in sent and a["pct"] < sent[k][1] + 0.5:
                continue
            if text is None:
                text = render(a, cfg, int(now - t_data), int(STORE.age(a["id"], now)))
            ok, code = tg_send2(cfg, text, kb_alert(a["id"]), chat)
            time.sleep(0.06)
            if ok:
                sent[k] = (now, a["pct"])
                per_user[chat] += 1
                delivered += 1
            elif code in (403, 400):                            # заблокировал бота / чат недоступен
                USERS.set(chat, active=False)
                log("подписчик %s отключён (HTTP %s)" % (chat, code))
    if delivered:
        log("отправлено сообщений: %d, подписчиков: %d" % (delivered, len(users)))


# ============================================================ шифрование данных сайта (AES-256-CTR + HMAC-SHA256, без внешних пакетов)

def _aes_tables():
    sbox, p, q = [0] * 256, 1, 1
    while True:                                                  # S-блок: обратный элемент в GF(2^8) + аффинное преобразование
        p = p ^ ((p << 1) & 0xFF) ^ (0x1B if p & 0x80 else 0)
        q ^= q << 1
        q ^= q << 2
        q ^= q << 4
        q &= 0xFF
        if q & 0x80:
            q ^= 0x09
        x = q ^ ((q << 1) | (q >> 7)) & 0xFF ^ ((q << 2) | (q >> 6)) & 0xFF ^ ((q << 3) | (q >> 5)) & 0xFF ^ ((q << 4) | (q >> 4)) & 0xFF
        sbox[p] = (x ^ 0x63) & 0xFF
        if p == 1:
            break
    sbox[0] = 0x63
    xt = lambda a: ((a << 1) ^ 0x11B) & 0xFF if a & 0x80 else a << 1
    t0 = [0] * 256
    for i in range(256):
        s = sbox[i]
        s2 = xt(s)
        t0[i] = (s2 << 24) | (s << 16) | (s << 8) | (s2 ^ s)
    return sbox, t0


_AES_SBOX, _AES_T0 = _aes_tables()


def _aes_expand(key):
    nk = len(key) // 4
    w = [int.from_bytes(key[4 * i:4 * i + 4], "big") for i in range(nk)]
    rc = 1
    for i in range(nk, 4 * (nk + 7)):
        t = w[i - 1]
        if i % nk == 0:
            t = ((t << 8) | (t >> 24)) & 0xFFFFFFFF
            t = (_AES_SBOX[t >> 24] << 24) | (_AES_SBOX[(t >> 16) & 255] << 16) | (_AES_SBOX[(t >> 8) & 255] << 8) | _AES_SBOX[t & 255]
            t ^= rc << 24
            rc = ((rc << 1) ^ 0x11B) & 0xFF if rc & 0x80 else rc << 1
        elif nk > 6 and i % nk == 4:
            t = (_AES_SBOX[t >> 24] << 24) | (_AES_SBOX[(t >> 16) & 255] << 16) | (_AES_SBOX[(t >> 8) & 255] << 8) | _AES_SBOX[t & 255]
        w.append(w[i - nk] ^ t)
    return w, nk + 6


def _aes_encrypt_block(w, rounds, blk):
    T0, S = _AES_T0, _AES_SBOX
    ror = lambda x, n: ((x >> n) | (x << (32 - n))) & 0xFFFFFFFF
    s0, s1, s2, s3 = (int.from_bytes(blk[i:i + 4], "big") ^ w[i // 4] for i in (0, 4, 8, 12))
    for r in range(1, rounds):
        k = 4 * r
        n0 = T0[s0 >> 24] ^ ror(T0[(s1 >> 16) & 255], 8) ^ ror(T0[(s2 >> 8) & 255], 16) ^ ror(T0[s3 & 255], 24) ^ w[k]
        n1 = T0[s1 >> 24] ^ ror(T0[(s2 >> 16) & 255], 8) ^ ror(T0[(s3 >> 8) & 255], 16) ^ ror(T0[s0 & 255], 24) ^ w[k + 1]
        n2 = T0[s2 >> 24] ^ ror(T0[(s3 >> 16) & 255], 8) ^ ror(T0[(s0 >> 8) & 255], 16) ^ ror(T0[s1 & 255], 24) ^ w[k + 2]
        n3 = T0[s3 >> 24] ^ ror(T0[(s0 >> 16) & 255], 8) ^ ror(T0[(s1 >> 8) & 255], 16) ^ ror(T0[s2 & 255], 24) ^ w[k + 3]
        s0, s1, s2, s3 = n0, n1, n2, n3
    k = 4 * rounds
    o = []
    for a, b, c, d, kk in ((s0, s1, s2, s3, w[k]), (s1, s2, s3, s0, w[k + 1]), (s2, s3, s0, s1, w[k + 2]), (s3, s0, s1, s2, w[k + 3])):
        o.append(((S[a >> 24] << 24) | (S[(b >> 16) & 255] << 16) | (S[(c >> 8) & 255] << 8) | S[d & 255]) ^ kk)
    return b"".join(x.to_bytes(4, "big") for x in o)


def aes_ctr(key, iv, data):
    """AES-CTR как в WebCrypto (счётчик — младшие 64 бита блока, big-endian). Шифрование = расшифрование."""
    w, rounds = _aes_expand(key)
    hi, lo = int.from_bytes(iv[:8], "big"), int.from_bytes(iv[8:], "big")
    out = bytearray()
    for i in range(0, len(data), 16):
        ks = _aes_encrypt_block(w, rounds, hi.to_bytes(8, "big") + ((lo + i // 16) & 0xFFFFFFFFFFFFFFFF).to_bytes(8, "big"))
        chunk = data[i:i + 16]
        out += bytes(a ^ b for a, b in zip(chunk, ks))
    return bytes(out)


_CODE_ABC = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789"        # 32 символа без похожих (I, O, 0, 1): 5 бит на символ


def new_code():
    return "".join(secrets.choice(_CODE_ABC) for _ in range(20))


def fmt_code(c):
    return "-".join(c[i:i + 5] for i in range(0, len(c), 5))


def norm_code(s):
    return "".join(ch for ch in str(s).upper() if ch in _CODE_ABC)


def web_encrypt(doc, codes):
    """doc -> файл сайта: данные сжаты и зашифрованы случайным ключом K, K положен «в конверты» по личным кодам подписчиков.
    Чужой код (или отозванный) конверта не найдёт. Ключ новый при каждой публикации, поэтому отзыв действует со следующего обновления."""
    plain = zlib.compress(json.dumps(doc, ensure_ascii=False, separators=(",", ":")).encode(), 9)
    K, iv = os.urandom(32), os.urandom(8) + bytes(8)
    ct = aes_ctr(K, iv, plain)
    mac = hmac.new(hashlib.sha256(b"mac" + K).digest(), iv + ct, hashlib.sha256).digest()
    keys = {}
    for code in codes:
        n = os.urandom(8) + bytes(8)
        keys[hashlib.sha256(("id:" + code).encode()).hexdigest()[:16]] = {
            "n": base64.b64encode(n).decode(), "w": base64.b64encode(aes_ctr(hashlib.sha256(("wrap:" + code).encode()).digest(), n, K)).decode()}
    return {"v": 2, "updated": doc.get("updated"), "iv": base64.b64encode(iv).decode(), "ct": base64.b64encode(ct).decode(),
            "mac": base64.b64encode(mac).decode(), "keys": keys}


# ============================================================ подписка на сайт (выдаёт админ в Telegram)

def is_admin(cfg, chat):
    return bool(cfg.get("chat_id")) and str(chat) == str(cfg["chat_id"])


def site_url(cfg):
    if cfg.get("web_url"):
        return cfg["web_url"]
    repo = cfg.get("web_repo") or ""
    return "https://%s.github.io/%s/" % tuple(repo.split("/", 1)) if "/" in repo else "(адрес сайта не настроен: web_repo)"


def has_site(cfg, chat):
    if is_admin(cfg, chat):
        return True
    u = USERS.get(chat) or {}
    return float(u.get("sub_until") or 0) > time.time()


def ensure_code(cfg, chat):
    u = USERS.get(chat)
    if u is None:
        USERS.add(cfg, chat, "владелец" if is_admin(cfg, chat) else str(chat))
        u = USERS.get(chat)
    if not u.get("site_code"):
        USERS.set(chat, site_code=new_code())
        u = USERS.get(chat)
    return u["site_code"]


def site_codes(cfg):
    """Коды всех, у кого сейчас есть доступ к сайту (подписчики с неистёкшей подпиской и владелец)."""
    out = []
    if cfg.get("chat_id"):
        out.append(ensure_code(cfg, cfg["chat_id"]))
    with USERS.lock:
        chats = [c for c in USERS.d if not is_admin(cfg, c)]
    for c in chats:
        if has_site(cfg, c):
            out.append(ensure_code(cfg, c))
    return out


def _until_txt(ts):
    return dt.datetime.fromtimestamp(float(ts), MSK).strftime("%d.%m.%Y")


def sub_text(cfg, chat):
    u = USERS.get(chat) or {}
    until = "бессрочно" if is_admin(cfg, chat) else "до %s" % _until_txt(u["sub_until"])
    return ("🌐 <b>Сайт с вилками</b>\nПодписка активна: <b>%s</b>\n\nАдрес: %s\nВаш личный код доступа (введите его на странице):\n<code>%s</code>\n\n"
            "Код личный, никому его не передавайте: он перестанет работать, когда подписка закончится или админ отключит доступ." %
            (until, site_url(cfg), fmt_code(ensure_code(cfg, chat))))


def sub_grant(cfg, chat, days):
    u = USERS.get(chat)
    if u is None:
        return None
    base = max(time.time(), float(u.get("sub_until") or 0))
    until = base + days * 86400
    ensure_code(cfg, chat)
    USERS.set(chat, sub_until=until, sub_warn=False, sub_end=False, site_req=0)
    web_publish_now(cfg)
    tg_send(cfg, "✅ Доступ к сайту открыт на %d дн.\n\n%s" % (days, sub_text(cfg, chat)), None, chat)
    return until


def sub_revoke(cfg, chat):
    USERS.set(chat, sub_until=0, site_req=0)
    web_publish_now(cfg)
    tg_send(cfg, "Доступ к сайту отключён. Вопросы — к администратору.", None, chat)


def sub_notices(cfg):
    """Предупреждение за сутки до конца подписки и сообщение об окончании (раз на каждую подписку)."""
    now = time.time()
    with USERS.lock:
        items = [(c, dict(u)) for c, u in USERS.d.items() if float(u.get("sub_until") or 0) > 0 and not is_admin(cfg, c)]
    for c, u in items:
        left = float(u["sub_until"]) - now
        if left <= 0 and not u.get("sub_end"):
            USERS.set(c, sub_end=True)
            tg_send(cfg, "⌛ Подписка на сайт закончилась. Чтобы продлить, откройте меню → «Сайт» и запросите доступ.", None, c)
            web_publish_now(cfg)
        elif 0 < left < 86400 and not u.get("sub_warn"):
            USERS.set(c, sub_warn=True)
            tg_send(cfg, "⏳ Подписка на сайт закончится %s. Чтобы продлить, откройте меню → «Сайт» → «Запросить доступ»." % _until_txt(u["sub_until"]), None, c)


def kb_site(cfg, chat):
    if has_site(cfg, chat):
        return {"inline_keyboard": [[btn("🎟 Ввести промокод", "spr")], [btn("🏠 Меню", "home")]]}
    return {"inline_keyboard": [[btn("📩 Запросить доступ", "sreq"), btn("🎟 Ввести промокод", "spr")], [btn("🏠 Меню", "home")]]}


def show_site(cfg, chat, mid):
    if has_site(cfg, chat):
        show(cfg, chat, mid, sub_text(cfg, chat), kb_site(cfg, chat))
    else:
        u = USERS.get(chat) or {}
        extra = "\n\nПодписка закончилась %s." % _until_txt(u["sub_until"]) if float(u.get("sub_until") or 0) > 0 else ""
        show(cfg, chat, mid, "🌐 <b>Сайт с вилками</b>\nДоступ к сайту по подписке. Нажмите «Запросить доступ» — администратор получит заявку."
             + extra, kb_site(cfg, chat))


def site_request(cfg, chat, mid):
    u = USERS.get(chat) or {}
    if time.time() - float(u.get("site_req") or 0) < 6 * 3600:
        show(cfg, chat, mid, "📩 Заявка уже отправлена администратору. Как только он откроет доступ, вам придёт сообщение с кодом.", kb_site(cfg, chat))
        return
    USERS.set(chat, site_req=time.time())
    show(cfg, chat, mid, "📩 Заявка отправлена. Как только администратор откроет доступ, вам придёт сообщение с кодом.", kb_site(cfg, chat))
    if cfg.get("chat_id"):
        tg_send(cfg, "📩 Заявка на доступ к сайту: %s (%s)" % (esc(u.get("name", "")), chat),
                {"inline_keyboard": [[btn("7 дн", "adg:%s:7" % chat), btn("30 дн", "adg:%s:30" % chat), btn("90 дн", "adg:%s:90" % chat)],
                                     [btn("Отклонить", "adn:%s" % chat), btn("👤 Карточка", "admc:%s" % chat)]]})



# ---------- промокоды на активацию подписки

class Promos:
    """Промокоды: код -> {days, uses, used:[chat], created}. Хранится в promos.json рядом с users.json."""

    def __init__(self, path):
        self.lock = threading.RLock()
        self.path, self.d, self.fails = path, {}, {}
        try:
            with open(path, encoding="utf-8") as fh:
                self.d = json.load(fh)
        except Exception:
            self.d = {}

    def save(self):
        with self.lock:
            try:
                tmp = self.path + ".tmp"
                with open(tmp, "w", encoding="utf-8") as fh:
                    json.dump(self.d, fh, ensure_ascii=False, indent=1)
                os.replace(tmp, self.path)
            except Exception as e:
                log("promos.json:", type(e).__name__)

    def create(self, days, uses):
        with self.lock:
            code = "".join(secrets.choice(_CODE_ABC) for _ in range(10))
            self.d[code] = {"days": int(days), "uses": int(uses), "used": [], "created": int(time.time())}
            self.save()
            return code

    def redeem(self, chat, raw):
        """-> (код, дней, None) при успехе или (None, 0, текст ошибки)."""
        code, now = norm_code(raw), time.time()
        with self.lock:
            recent = [t for t in self.fails.get(str(chat), []) if now - t < 3600]
            if len(recent) >= 5:
                return None, 0, "Слишком много неверных попыток. Попробуйте через час."
            pr = self.d.get(code) if len(code) == 10 else None
            if pr is None:
                self.fails[str(chat)] = recent + [now]
                return None, 0, "Такого промокода нет. Проверьте, что ввели его без ошибок."
            if str(chat) in pr["used"]:
                return None, 0, "Вы уже активировали этот промокод."
            if len(pr["used"]) >= pr["uses"]:
                return None, 0, "Промокод уже исчерпан."
            pr["used"].append(str(chat))
            self.save()
            return code, pr["days"], None


PROMOS = Promos("promos.json")


def fmt_promo(c):
    return c[:5] + "-" + c[5:]


def promo_redeem(cfg, chat, raw, mid=None):
    u = USERS.get(chat)
    if u is None:
        return False
    code, days, err = PROMOS.redeem(chat, raw)
    if err:
        tg_send(cfg, "🎟 " + err, {"inline_keyboard": [[btn("🎟 Ввести ещё раз", "spr"), btn("🏠 Меню", "home")]]}, chat)
        return True
    sub_grant(cfg, chat, days)
    left = PROMOS.d[code]["uses"] - len(PROMOS.d[code]["used"])
    if cfg.get("chat_id"):
        tg_send(cfg, "🎟 Промокод <code>%s</code> активирован: %s (%s), +%d дн. Осталось активаций: %d" %
                (fmt_promo(code), esc(u.get("name", "")), chat, days, left))
    return True


def show_promos(cfg, chat, mid):
    with PROMOS.lock:
        items = sorted(PROMOS.d.items(), key=lambda x: -x[1].get("created", 0))
    rows = [[btn("➕ 7 дн · 1 раз", "prn:7:1"), btn("➕ 30 дн · 1 раз", "prn:30:1")],
            [btn("➕ 90 дн · 1 раз", "prn:90:1"), btn("➕ 30 дн · 10 раз", "prn:30:10")]]
    for c, pr in items[:12]:
        left = pr["uses"] - len(pr["used"])
        rows.append([btn("%s · %d дн · осталось %d/%d" % (fmt_promo(c), pr["days"], left, pr["uses"]), "prc:" + c)])
    rows.append([btn("⬅️ Админ-панель", "adm")])
    show(cfg, chat, mid, "🎟 <b>Промокоды</b>\nНажмите «➕», чтобы создать код. Подписчик вводит его в боте: меню → «Сайт» → «Ввести промокод» "
         "или командой <code>/promo КОД</code>.\nСвой набор: <code>/promo_new ДНИ ЧИСЛО_АКТИВАЦИЙ</code>.", {"inline_keyboard": rows})


def promo_callback(cfg, chat, mid, data):
    if data == "spr":
        view(chat)["pending_promo"] = True
        show(cfg, chat, mid, "🎟 Отправьте промокод одним сообщением (например <code>ABCDE-FGHIJ</code>).", {"inline_keyboard": [[btn("🏠 Меню", "home")]]})
        return True
    if not (data == "prm" or data.startswith(("prn:", "prc:", "prd:"))):
        return False
    if not is_admin(cfg, chat):
        return True
    p = data.split(":")
    try:
        if data == "prm":
            show_promos(cfg, chat, mid)
        elif p[0] == "prn":
            code = PROMOS.create(int(p[1]), int(p[2]))
            tg_send(cfg, "🎟 Новый промокод: <code>%s</code>\n%d дн., активаций: %d" % (fmt_promo(code), int(p[1]), int(p[2])), None, chat)
            show_promos(cfg, chat, mid)
        elif p[0] == "prc":
            pr = PROMOS.d.get(p[1])
            if pr:
                show(cfg, chat, mid, "🎟 <code>%s</code>\n%d дн. · использовано %d из %d" % (fmt_promo(p[1]), pr["days"], len(pr["used"]), pr["uses"]),
                     {"inline_keyboard": [[btn("🗑 Удалить", "prd:" + p[1])], [btn("⬅️ К промокодам", "prm")]]})
            else:
                show_promos(cfg, chat, mid)
        elif p[0] == "prd":
            PROMOS.d.pop(p[1], None)
            PROMOS.save()
            show_promos(cfg, chat, mid)
    except (ValueError, IndexError):
        pass
    return True


# ---------- админ-панель

ADM_PAGE = 8


def adm_status(cfg, chat, u):
    if is_admin(cfg, chat):
        return "владелец"
    t = float(u.get("sub_until") or 0)
    return ("до " + _until_txt(t)) if t > time.time() else ("закончилась " + _until_txt(t) if t else "нет")


def _asks(cfg, c, u):
    return time.time() - float(u.get("site_req") or 0) < 7 * 86400 and not has_site(cfg, c)


def show_admin(cfg, chat, mid):
    with USERS.lock:
        users = list(USERS.d.items())
    act = sum(1 for c, u in users if has_site(cfg, c) and not is_admin(cfg, c))
    req = sum(1 for c, u in users if _asks(cfg, c, u))
    show(cfg, chat, mid, "🛠 <b>Админ-панель</b>\nПользователей: %d\nС доступом к сайту: %d\nЗаявок на доступ: %d\n\n"
         "Быстрые команды:\n<code>/grant ID ДНИ</code> — выдать или продлить\n<code>/revoke ID</code> — отключить" % (len(users), act, req),
         {"inline_keyboard": [[btn("👥 Пользователи", "admu:0"), btn("🎟 Промокоды", "prm")], [btn("🏠 Меню", "home")]]})


def show_admin_users(cfg, chat, mid, page):
    with USERS.lock:
        users = [(c, dict(u)) for c, u in USERS.d.items()]
    users.sort(key=lambda x: (0 if _asks(cfg, x[0], x[1]) else 1, -float(x[1].get("joined") or 0)))
    n = (len(users) + ADM_PAGE - 1) // ADM_PAGE or 1
    page = max(0, min(page, n - 1))
    rows = []
    for c, u in users[page * ADM_PAGE:(page + 1) * ADM_PAGE]:
        mark = "📩 " if _asks(cfg, c, u) else ("✅ " if has_site(cfg, c) else "")
        rows.append([btn("%s%s · %s" % (mark, (u.get("name") or str(c))[:22], adm_status(cfg, c, u)), "admc:%s" % c)])
    nav = []
    if page > 0:
        nav.append(btn("⬅️", "admu:%d" % (page - 1)))
    nav.append(btn("%d / %d" % (page + 1, n), "noop"))
    if page < n - 1:
        nav.append(btn("➡️", "admu:%d" % (page + 1)))
    rows += [nav, [btn("⬅️ Админ-панель", "adm")]]
    show(cfg, chat, mid, "👥 <b>Пользователи</b>\n📩 — просит доступ, ✅ — доступ есть", {"inline_keyboard": rows})


def show_admin_user(cfg, chat, mid, target):
    u = USERS.get(target)
    if u is None:
        show(cfg, chat, mid, "Пользователь не найден.", {"inline_keyboard": [[btn("⬅️ К списку", "admu:0")]]})
        return
    code = fmt_code(u["site_code"]) if u.get("site_code") else "ещё не выдан"
    show(cfg, chat, mid, "👤 <b>%s</b>\nID: <code>%s</code>\nВ боте с: %s\nПодписка на сайт: <b>%s</b>\nКод доступа: <code>%s</code>" %
         (esc(u.get("name", "")), target, _until_txt(u.get("joined") or time.time()), adm_status(cfg, target, u), code),
         {"inline_keyboard": [[btn("+7 дн", "adg:%s:7" % target), btn("+30 дн", "adg:%s:30" % target), btn("+90 дн", "adg:%s:90" % target)],
                              [btn("❌ Отозвать доступ", "adr:%s" % target), btn("🔑 Новый код", "adk:%s" % target)],
                              [btn("⬅️ К списку", "admu:0")]]})


def admin_callback(cfg, chat, mid, data):
    """Колбэки админ-панели и подписки. -> True, если обработано. Админские — только для владельца."""
    if data == "site":
        show_site(cfg, chat, mid)
        return True
    if data == "sreq":
        site_request(cfg, chat, mid)
        return True
    if promo_callback(cfg, chat, mid, data):
        return True
    if not (data == "adm" or data.startswith(("admu:", "admc:", "adg:", "adr:", "adk:", "adn:"))):
        return False
    if not is_admin(cfg, chat):
        return True
    p = data.split(":")
    try:
        if data == "adm":
            show_admin(cfg, chat, mid)
        elif p[0] == "admu":
            show_admin_users(cfg, chat, mid, int(p[1]))
        elif p[0] == "admc":
            show_admin_user(cfg, chat, mid, p[1])
        elif p[0] == "adg":
            if sub_grant(cfg, p[1], int(p[2])) is None:
                tg_send(cfg, "Пользователь %s не найден (он должен сначала написать боту /start)." % p[1], None, chat)
            else:
                show_admin_user(cfg, chat, mid, p[1])
        elif p[0] == "adr":
            sub_revoke(cfg, p[1])
            show_admin_user(cfg, chat, mid, p[1])
        elif p[0] == "adk":
            if USERS.get(p[1]) is not None:
                USERS.set(p[1], site_code=new_code())
                web_publish_now(cfg)
                if has_site(cfg, p[1]):
                    tg_send(cfg, "🔑 Ваш код доступа к сайту обновлён:\n<code>%s</code>" % fmt_code(USERS.get(p[1])["site_code"]), None, p[1])
            show_admin_user(cfg, chat, mid, p[1])
        elif p[0] == "adn":
            USERS.set(p[1], site_req=0)
            tg_send(cfg, "Заявка на доступ к сайту отклонена администратором.", None, p[1])
            show(cfg, chat, mid, "Заявка отклонена.", {"inline_keyboard": [[btn("🛠 Админ-панель", "adm")]]})
    except (ValueError, IndexError):
        pass
    return True


# ============================================================ сайт (GitHub Pages): телефон кладёт arbs.json в репозиторий, страница читает его

WEB = {"t": 0.0, "sha": None, "busy": False, "fails": 0}


def web_payload(cands, cfg, now, t_data, info):
    """Вилки для сайта: денежные (прибыль > 0) и фрибетные, без привязки к Telegram. Сами фильтры (БК, сегодня, прибыль) — на странице."""
    items = []
    for a in cands:
        if not acceptable(a, cfg) or (a["mode"] == "cash" and a["pct"] <= 0):
            continue
        ev = a["event"]
        items.append({
            "id": a.get("id") or arb_id(a), "mode": a["mode"], "pct": round(a["pct"], 2), "start": int(ev["start"]),
            "home": ev["home"], "away": ev["away"], "sport": a["fon"].get("sport") or "Футбол", "league": a["fon"].get("league") or "",
            "fb_bk": a.get("fb_bk", ""), "base": a["base_sum"] if a["mode"] == "freebet" else 0,
            "bets": [{"bk": bk, "o": _html.unescape(bet_label(a, o, bk)), "k": round(v, 3)} for o, bk, v, _ in a["stakes"]]})
    cash = [x for x in items if x["mode"] == "cash"]
    fb = sorted((x for x in items if x["mode"] == "freebet"), key=lambda x: -x["pct"])[:int(cfg.get("web_max_freebet", 400))]
    items = sorted(cash + fb, key=lambda x: (x["start"], -x["pct"]))
    return {"updated": int(now), "data_t": int(t_data), "info": info, "bk": BK_TITLE, "usd": usd_rate(cfg) or 0, "arbs": items}


def _gh(cfg, method, path, body=None, timeout=60):
    req = urllib.request.Request("https://api.github.com" + path, method=method,
                                 data=json.dumps(body).encode() if body is not None else None,
                                 headers={"Authorization": "Bearer " + cfg["web_token"], "Accept": "application/vnd.github+json",
                                          "User-Agent": "arbphone", "X-GitHub-Api-Version": "2022-11-28", "Content-Type": "application/json"})
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return json.loads(r.read() or b"{}")


def _web_branch(cfg):
    repo, br = cfg["web_repo"], cfg["web_branch"]
    try:
        _gh(cfg, "GET", "/repos/%s/git/ref/heads/%s" % (repo, br))
        return
    except urllib.error.HTTPError as e:
        if e.code != 404:
            raise
    d = _gh(cfg, "GET", "/repos/%s" % repo)["default_branch"]
    sha = _gh(cfg, "GET", "/repos/%s/git/ref/heads/%s" % (repo, d))["object"]["sha"]
    _gh(cfg, "POST", "/repos/%s/git/refs" % repo, {"ref": "refs/heads/" + br, "sha": sha})
    log("сайт: создана ветка %s" % br)



# ============================================================ несколько телефонов: «работник», автообновление, установщик, прогрев сайтов

VERSION = 78
REMOTE = {"sha": {}, "data": {}}
WORKER_LAST = {}
CODE_STATE = {"t": 0.0}
CL_BKS = ("polymarket", "onewin", "marathon", "olimp", "ligastavok", "leon", "betcity", "betboom", "fonbet", "winline")
FAST_BKS = ("fonbet", "winline")                                       # котировки быстро устаревают — у них свой, короткий срок годности


def _gh_bytes(cfg, path, timeout=60):
    """Содержимое файла из репозитория (raw, до 100 МБ) -> bytes; 404 -> None."""
    req = urllib.request.Request("https://api.github.com" + path, headers={
        "Authorization": "Bearer " + cfg["web_token"], "Accept": "application/vnd.github.raw+json", "User-Agent": "arbphone",
        "X-GitHub-Api-Version": "2022-11-28"})
    try:
        with urllib.request.urlopen(req, timeout=timeout) as r:
            return r.read()
    except urllib.error.HTTPError as e:
        if e.code == 404:
            return None
        raise


def _gh_sha(cfg, path):
    try:
        return _gh(cfg, "GET", "/repos/%s/contents/%s?ref=%s" % (cfg["web_repo"], path, cfg["web_branch"])).get("sha")
    except urllib.error.HTTPError as e:
        if e.code == 404:
            return None
        raise


def gh_put(cfg, path, data, msg, tries=3):
    """Записать файл в ветку данных (создаёт или заменяет)."""
    _web_branch(cfg)
    for k in range(tries):
        body = {"message": msg, "branch": cfg["web_branch"], "content": base64.b64encode(data).decode()}
        sha = _gh_sha(cfg, path)
        if sha:
            body["sha"] = sha
        try:
            return _gh(cfg, "PUT", "/repos/%s/contents/%s" % (cfg["web_repo"], path), body, timeout=120)
        except urllib.error.HTTPError as e:
            if e.code in (409, 422, 502, 503, 504) and k < tries - 1:
                time.sleep(2 + 3 * k)
                continue
            raise


def fetch_bk(cfg, bk):
    """Опрос одной БК (для телефона-работника) -> (события, время снимка)."""
    now = time.time()
    if bk == "polymarket":
        return polymarket_fetch(cfg), PM_CACHE["t"] or now
    if bk == "onewin":
        return onewin_fetch(cfg), OW_CACHE["t"] or now
    if bk == "marathon":
        return marathon_fetch(cfg), MA_CACHE["t"] or now
    if bk == "olimp":
        return olimp_fetch(cfg), OL_CACHE["t"] or now
    if bk == "ligastavok":
        return ls_events(ls_fetch(cfg)), LS_CACHE["t"] or now
    if bk == "leon":
        if time.time() < LEON_CACHE.get("pause", 0):
            return [], None
        if not (LEON_CACHE["ev"] and time.time() - LEON_CACHE["t"] <= cfg["leon_ttl"]):
            LEON_CACHE["ev"] = leon_events(leon_fetch(cfg))
            LEON_CACHE["t"] = time.time()
        return LEON_CACHE["ev"], LEON_CACHE["t"]
    if bk == "betcity":
        return betcity_events(betcity_fetch(cfg)), BC_CACHE["t"] or now
    if bk == "betboom":
        msgs, names = betboom_fetch(cfg)
        return bb_events(msgs, names, now=time.time()), time.time()
    if bk == "fonbet":
        ev = fonbet_parse(fonbet_fetch(cfg))
        return ev, time.time()
    if bk == "winline":
        ev = winline_events(winline_fetch(cfg))
        return ev, time.time()
    raise ValueError("работник не умеет опрашивать: " + bk)


def worker_cycle(cfg):
    wid = cfg.get("worker_id") or "worker"
    for bk in cfg.get("bks") or []:
        if bk in FAST_BKS:                                      # Фонбет/Винлайн — в отдельном быстром потоке
            continue
        if bk not in CL_BKS:
            log("работник: неизвестная БК «%s» (доступны: %s)" % (bk, ", ".join(CL_BKS)))
            continue
        try:
            ev, t = fetch_bk(cfg, bk)
            if ev and t:
                WORKER_LAST[bk] = {"t": t, "ev": ev}
            log("работник %s: %s — %d матчей" % (wid, bk, len(ev)))
        except SystemExit:
            raise
        except Exception as e:
            log("работник: %s недоступна: %s: %s" % (bk, type(e).__name__, e))
    if not WORKER_LAST:
        return
    for k in [k for k in WORKER_LAST if k in FAST_BKS]:
        del WORKER_LAST[k]
    doc = {"id": wid, "v": VERSION, "t": time.time(), "bk": WORKER_LAST}
    raw = gzip.compress(json.dumps(doc, ensure_ascii=False, separators=(",", ":"), default=str).encode("utf-8"), 6)
    gh_put(cfg, "workers/%s.json.gz" % re.sub(r"[^\w.-]", "_", wid), raw, "worker " + wid)
    log("работник %s: опубликовано %d КБ (%s)" % (wid, len(raw) // 1024, ", ".join(sorted(WORKER_LAST))))


def remote_load(cfg):
    """Главный телефон: прочитать файлы работников (только изменившиеся)."""
    try:
        lst = _gh(cfg, "GET", "/repos/%s/contents/workers?ref=%s" % (cfg["web_repo"], cfg["web_branch"]))
    except urllib.error.HTTPError as e:
        if e.code == 404:
            return
        raise
    for f in lst:
        name = f.get("name", "")
        if not name.endswith(".json.gz") or REMOTE["sha"].get(name) == f.get("sha"):
            continue
        raw = _gh_bytes(cfg, "/repos/%s/contents/workers/%s?ref=%s" % (cfg["web_repo"], name, cfg["web_branch"]))
        if raw:
            REMOTE["data"][name] = json.loads(gzip.decompress(raw).decode("utf-8"))
            REMOTE["sha"][name] = f.get("sha")
            log("работник %s: получены данные (%s)" % (REMOTE["data"][name].get("id"), ", ".join(sorted(REMOTE["data"][name].get("bk", {})))))


def remote_events(cfg, bk):
    """Свежие события БК от работников -> (события, время снимка) или ([], None)."""
    best = None
    for doc in REMOTE["data"].values():
        d = (doc.get("bk") or {}).get(bk)
        if d and (best is None or d["t"] > best["t"]):
            best = d
    limit = cfg.get("remote_fast_age", 420) if bk in FAST_BKS else cfg.get("remote_max_age", 1200)
    if not best or time.time() - best["t"] > limit:
        return [], None
    return [e for e in best["ev"] if e.get("start", 0) > time.time()], best["t"]


def _code_files(cfg):
    return {"code/arbphone.py": open(os.path.abspath(__file__), "rb").read(),
            "code/install.sh": install_script(cfg).encode()}


def install_script(cfg):
    return r'''#!/data/data/com.termux/files/usr/bin/bash
# Установка телефона-работника ArbPhone (запускать в Termux одной командой)
REPO="%(repo)s"; BR="%(br)s"
echo "== ArbPhone: установка работника =="
pkg update -y >/dev/null 2>&1
pkg install -y python curl tmux termux-api >/dev/null 2>&1 || pkg install -y python curl tmux
pip install --break-system-packages websocket-client >/dev/null 2>&1 || pip install websocket-client
mkdir -p ~/arb && cd ~/arb || exit 1
read -r -p "Имя телефона (например tel2): " WID </dev/tty
read -r -s -p "Токен GitHub (вставьте и нажмите Enter): " TOK </dev/tty; echo
curl -fsSL -H "Authorization: Bearer $TOK" -H "Accept: application/vnd.github.raw+json" \
  "https://api.github.com/repos/$REPO/contents/code/arbphone.py?ref=$BR" -o arbphone.py || { echo "Не удалось скачать бота: проверьте токен"; exit 1; }
WID="$WID" TOK="$TOK" REPO="$REPO" BR="$BR" python - <<'PY'
import json, os
cfg = {"role": "worker", "worker_id": os.environ["WID"], "bks": [],
       "web_repo": os.environ["REPO"], "web_token": os.environ["TOK"], "web_branch": os.environ["BR"]}
json.dump(cfg, open("config.json", "w"), ensure_ascii=False, indent=2)
PY
termux-wake-lock 2>/dev/null
tmux kill-session -t arb 2>/dev/null
tmux new-session -d -s arb "cd ~/arb && python arbphone.py"
echo "Готово. Работник запущен. Смотреть: tmux attach -t arb   (выйти: Ctrl+B, затем D)"
''' % {"repo": cfg["web_repo"], "br": cfg["web_branch"]}


def code_sync(cfg, role):
    """Главный телефон выкладывает свой код в репозиторий (если версия новее); работник и (по желанию) главный обновляются из него."""
    if not (cfg.get("web_repo") and cfg.get("web_token")):
        return
    raw = _gh_bytes(cfg, "/repos/%s/contents/code/VERSION?ref=%s" % (cfg["web_repo"], cfg["web_branch"]))
    try:
        rv = int((raw or b"0").strip() or 0)
    except ValueError:
        rv = 0
    if VERSION > rv and role == "main":
        for path, data in _code_files(cfg).items():
            gh_put(cfg, path, data, "code v%d" % VERSION)
        gh_put(cfg, "code/VERSION", str(VERSION).encode(), "code v%d" % VERSION)
        log("код версии %d выложен в репозиторий (телефоны-работники обновятся сами)" % VERSION)
    elif rv > VERSION and (cfg.get("auto_update") if cfg.get("auto_update") is not None else role == "worker"):
        src = _gh_bytes(cfg, "/repos/%s/contents/code/arbphone.py?ref=%s" % (cfg["web_repo"], cfg["web_branch"]))
        if not src or ("VERSION = %d" % rv).encode() not in src:
            log("автообновление: в репозитории код не той версии — пропускаю")
            return
        compile(src, "arbphone.py", "exec")                              # синтаксис проверен до замены
        me = os.path.abspath(__file__)
        with open(me + ".new", "wb") as fh:
            fh.write(src)
        os.replace(me + ".new", me)
        log("автообновление: версия %d -> %d, перезапускаюсь" % (VERSION, rv))
        os.execv(sys.executable, [sys.executable] + sys.argv)


def code_sync_safe(cfg, role):
    if time.time() - CODE_STATE["t"] < cfg.get("update_every", 600):
        return
    CODE_STATE["t"] = time.time()
    try:
        code_sync(cfg, role)
    except SystemExit:
        raise
    except Exception as e:
        log("обновление кода: %s: %s" % (type(e).__name__, e))


KEEP_URL = {"betcity": "https://betcity.ru/", "betboom": "https://betboom.ru/", "ligastavok": "https://www.ligastavok.ru/", "olimp": "https://www.olimp.bet/"}


def keepalive_loop(cfg, sites):
    """Периодически открывает сайты БК в браузере телефона (прогрев, чтобы не было блокировок)."""
    if not sites or not shutil.which("termux-open-url"):
        return
    log("прогрев сайтов: каждые %d мин открываю %s" % (cfg.get("keepalive_every", 900) // 60, ", ".join(sites)))
    while True:
        time.sleep(cfg.get("keepalive_every", 900))
        for bk in sites:
            try:
                subprocess.run(["termux-open-url", KEEP_URL[bk]], timeout=20, capture_output=True)
            except Exception as e:
                log("прогрев %s: %s" % (bk, type(e).__name__))
            time.sleep(25)


def keepalive_sites(cfg, local_bks):
    if not cfg.get("keepalive", True):
        return []
    return [b for b in KEEP_URL if b in local_bks]


FLEET = {"etag": None, "assign": {}, "hb": 0.0, "started": time.time()}


def device_info():
    """Модель и версия Android телефона (через getprop; на обычном ПК — имя машины)."""
    def gp(k):
        try:
            return subprocess.run(["getprop", k], capture_output=True, text=True, timeout=5).stdout.strip()
        except Exception:
            return ""
    model = (gp("ro.product.manufacturer") + " " + gp("ro.product.model")).strip()
    return {"model": model or socket.gethostname(), "android": gp("ro.build.version.release")}


def heartbeat(cfg, ident, role, status, extra=None, force=False):
    """Карточка телефона для сайта: fleet/<имя>.json (не чаще heartbeat_every сек)."""
    if not force and time.time() - FLEET["hb"] < cfg.get("heartbeat_every", 240):
        return
    FLEET["hb"] = time.time()
    doc = dict(device_info(), id=ident, role=role, v=VERSION, t=int(time.time()), started=int(FLEET["started"]), status=status)
    doc.update(extra or {})
    try:
        gh_put(cfg, "fleet/%s.json" % re.sub(r"[^\w.-]", "_", ident), json.dumps(doc, ensure_ascii=False).encode("utf-8"), "hb " + ident)
    except SystemExit:
        raise
    except Exception as e:
        log("карточка телефона: %s: %s" % (type(e).__name__, e))


def fleet_sync(cfg):
    """Назначения с сайта (fleet.json): какие БК опрашивает каждый телефон и пауза/старт. True — изменилось."""
    hdr = {"Authorization": "Bearer " + cfg["web_token"], "Accept": "application/vnd.github.raw+json", "User-Agent": "arbphone",
           "X-GitHub-Api-Version": "2022-11-28"}
    if FLEET["etag"]:
        hdr["If-None-Match"] = FLEET["etag"]
    req = urllib.request.Request("https://api.github.com/repos/%s/contents/fleet.json?ref=%s" % (cfg["web_repo"], cfg["web_branch"]), headers=hdr)
    try:
        with urllib.request.urlopen(req, timeout=20) as r:
            FLEET["etag"] = r.headers.get("ETag")
            new = (json.loads(r.read().decode("utf-8", "replace")) or {}).get("phones") or {}
    except urllib.error.HTTPError as e:
        if e.code in (304, 404):
            return False
        raise
    changed = new != FLEET["assign"]
    FLEET["assign"] = new
    return changed


FAST = {"bks": [], "run": False, "thread": None, "last": {}}


def worker_fast_loop(cfg, wid):
    """Отдельный поток: Фонбет/Винлайн опрашиваются часто (worker_fast_interval) и публикуются в свой файл — медленные БК их не задерживают."""
    while True:
        bks = [b for b in FAST["bks"] if b in FAST_BKS]
        if not (bks and FAST["run"]):
            time.sleep(5)
            continue
        t0 = time.time()
        for bk in bks:
            try:
                ev, t = fetch_bk(cfg, bk)
                if ev:
                    FAST["last"][bk] = {"t": t, "ev": ev}
                log("работник %s: %s — %d матчей" % (wid, bk, len(ev)))
            except SystemExit:
                raise
            except Exception as e:
                log("работник: %s недоступна: %s: %s" % (bk, type(e).__name__, e))
        for k in [k for k in FAST["last"] if k not in bks]:
            del FAST["last"][k]
        if FAST["last"]:
            try:
                doc = {"id": wid + "-fast", "v": VERSION, "t": time.time(), "bk": FAST["last"]}
                raw = gzip.compress(json.dumps(doc, ensure_ascii=False, separators=(",", ":"), default=str).encode("utf-8"), 6)
                gh_put(cfg, "workers/%s__fast.json.gz" % re.sub(r"[^\w.-]", "_", wid), raw, "fast " + wid)
                log("работник %s: Фонбет/Винлайн опубликованы, %d КБ" % (wid, len(raw) // 1024))
            except SystemExit:
                raise
            except Exception as e:
                log("работник: публикация %s: %s" % (type(e).__name__, e))
        time.sleep(max(5.0, cfg.get("worker_fast_interval", 60) - (time.time() - t0)))


def worker_main(cfg):
    if not (cfg.get("web_repo") and cfg.get("web_token")):
        sys.exit("Работнику нужны web_repo и web_token в config.json")
    wid = cfg.get("worker_id") or socket.gethostname()
    base_bks = list(cfg.get("bks") or [])
    log("ArbPhone-работник «%s», версия %d (%s)" % (wid, VERSION, device_info()["model"]))
    state = {"bks": [], "paused": False}
    due = 0.0
    sites_thread = [None]
    while True:
        try:
            if fleet_sync(cfg):
                log("назначения с сайта изменились")
        except SystemExit:
            raise
        except Exception as e:
            log("назначения с сайта: %s: %s" % (type(e).__name__, e))
        if time.time() - state.get("set_t", 0) >= cfg.get("settings_poll", 30):
            state["set_t"] = time.time()
            try:
                settings_sync(cfg)
            except SystemExit:
                raise
            except Exception as e:
                log("настройки с сайта: %s: %s" % (type(e).__name__, e))
        mine = FLEET["assign"].get(wid) or {}
        bks = [b for b in (mine.get("bks") if "bks" in mine else base_bks) if b in CL_BKS]
        paused = bool(mine.get("paused", False))
        if (bks, paused) != (state["bks"], state["paused"]):
            state.update(bks=bks, paused=paused)
            for k in list(WORKER_LAST):
                if k not in bks:
                    del WORKER_LAST[k]
            due = 0.0
            heartbeat(cfg, wid, "worker", "пауза" if paused else ("ждёт назначения БК с сайта" if not bks else "парсит"), {"bks": bks, "paused": paused}, force=True)
        FAST["bks"], FAST["run"] = [b for b in bks if b in FAST_BKS], not paused
        if FAST["thread"] is None:
            FAST["thread"] = threading.Thread(target=worker_fast_loop, args=(cfg, wid), daemon=True)
            FAST["thread"].start()
        if sites_thread[0] is None and bks and not paused:
            sites_thread[0] = threading.Thread(target=keepalive_loop, args=(cfg, keepalive_sites(cfg, bks)), daemon=True)
            sites_thread[0].start()
        code_sync_safe(cfg, "worker")
        if bks and not paused and time.time() >= due:
            t0 = time.time()
            cfg["bks"] = bks
            try:
                worker_cycle(cfg)
            except SystemExit:
                raise
            except Exception as e:
                log("ошибка цикла работника: %s: %s" % (type(e).__name__, e))
            due = time.time() + max(5.0, cfg.get("worker_interval", 120) - (time.time() - t0))
            heartbeat(cfg, wid, "worker", "парсит", {"bks": bks, "paused": False, "counts": {k: len(v["ev"]) for k, v in list(WORKER_LAST.items()) + list(FAST["last"].items())},
                                                     "cycle": int(time.time() - t0)})
        elif not bks or paused:
            heartbeat(cfg, wid, "worker", "пауза" if paused else "ждёт назначения БК с сайта", {"bks": bks, "paused": paused})
        time.sleep(15)


def _web_file():
    return os.path.join(os.path.dirname(USERS.path), "web_last.json")


def _web_save(payload):
    """Последние данные для сайта на диск: после перезапуска бота доступы выдаются сразу, не дожидаясь первого цикла."""
    try:
        tmp = _web_file() + ".tmp"
        with open(tmp, "w", encoding="utf-8") as fh:
            json.dump(payload, fh, ensure_ascii=False, separators=(",", ":"))
        os.replace(tmp, _web_file())
    except Exception as e:
        log("web_last.json:", type(e).__name__)


def web_restore(cfg):
    """При старте: подхватить сохранённые данные и сразу опубликовать (актуальные списки доступа, данные пока прошлые)."""
    if not (cfg.get("web_repo") and cfg.get("web_token")):
        return
    try:
        with open(_web_file(), encoding="utf-8") as fh:
            WEB["payload"] = json.load(fh)
    except Exception:
        return
    web_publish(cfg, WEB["payload"], force=True)
    log("сайт: после запуска опубликованы сохранённые данные (возраст %d мин), доступы актуальны" % ((time.time() - WEB["payload"].get("updated", 0)) // 60))


def web_publish_now(cfg):
    """Сразу опубликовать последние данные (после выдачи/отзыва доступа), не дожидаясь следующего цикла."""
    if WEB.get("payload") and cfg.get("web_repo") and cfg.get("web_token"):
        web_publish(cfg, WEB["payload"], force=True)


def web_publish(cfg, payload, force=False):
    """Записать arbs.json в репозиторий (в фоне, не чаще web_every секунд). Ошибки только в лог."""
    if not cfg.get("web_repo") or not cfg.get("web_token"):
        return
    if payload is not WEB.get("payload"):
        WEB["payload"] = payload
        _web_save(payload)
    if WEB["busy"]:
        if force:
            WEB["dirty"] = True
        return
    if not force and time.time() - WEB["t"] < float(cfg.get("web_every", 60)):
        return
    WEB["busy"], WEB["t"] = True, time.time()

    def run():
        try:
            repo, br = cfg["web_repo"], cfg["web_branch"]
            doc = web_encrypt(WEB["payload"], site_codes(cfg)) if cfg.get("web_private", True) else WEB["payload"]
            data = base64.b64encode(json.dumps(doc, ensure_ascii=False, separators=(",", ":")).encode()).decode()
            for attempt in (1, 2, 3):
                try:
                    if WEB["sha"] is None:
                        try:
                            WEB["sha"] = _gh(cfg, "GET", "/repos/%s/contents/arbs.json?ref=%s" % (repo, br)).get("sha") or ""
                        except urllib.error.HTTPError as e:
                            if e.code != 404:
                                raise
                            _web_branch(cfg)
                            WEB["sha"] = ""
                    body = {"message": "arbs", "content": data, "branch": br}
                    if WEB["sha"]:
                        body["sha"] = WEB["sha"]
                    r = _gh(cfg, "PUT", "/repos/%s/contents/arbs.json" % repo, body)
                    WEB["sha"], WEB["fails"] = r["content"]["sha"], 0
                    if not WEB.get("logged"):
                        WEB["logged"] = True
                        log("сайт: arbs.json обновлён (%d КБ, вилок %d, доступ у %d)%s" % (len(data) * 3 // 4 // 1024, len(WEB["payload"]["arbs"]),
                                                                                  len(doc.get("keys", {})) if "keys" in doc else 0, "" if "keys" in doc else " — НЕ зашифровано"))
                    return
                except urllib.error.HTTPError as e:
                    if (e.code in (409, 422) or e.code in (502, 503, 504)) and attempt < 3:
                        WEB["sha"] = None                       # устарел sha / сбой GitHub — читаем заново и повторяем
                        time.sleep(2)
                        continue
                    raise
        except Exception as e:
            WEB["fails"] += 1
            WEB["sha"] = None
            code = getattr(e, "code", "")
            log("сайт: не удалось обновить arbs.json (%s %s)%s" % (type(e).__name__, code,
                " — проверьте web_repo/web_token" if code in (401, 403, 404) else ""))
        finally:
            WEB["busy"] = False
            if WEB.pop("dirty", False):
                web_publish(cfg, WEB["payload"], force=True)
    threading.Thread(target=run, daemon=True).start()


def main():
    ap = argparse.ArgumentParser(description="ArbPhone: Фонбет + Винлайн + БетБум -> вилки в Telegram")
    ap.add_argument("--config")
    ap.add_argument("--once", action="store_true", help="один цикл и выход")
    ap.add_argument("--no-send", action="store_true", help="печатать вместо отправки в Telegram")
    ap.add_argument("--near", type=int, default=0, help="показать N ближайших к вилке кандидатов")
    ap.add_argument("--show", help="показать коэффициенты обеих БК по матчу (часть названия команды), для сверки")
    ap.add_argument("--probe", type=int, metavar="N", help="собрать данные по N матчам для калибровки угловых и отправить probe.json в Telegram")
    ap.add_argument("--qc", action="store_true", help="контроль качества разбора Винлайна против Фонбета")
    ap.add_argument("--har-fonbet", help="офлайн-тест: HAR-файл Фонбета")
    ap.add_argument("--har-winline", help="офлайн-тест: HAR-файл Винлайна")
    ap.add_argument("--betcity-test", action="store_true", help="проверка Бетсити: один запрос по футболу с подробным выводом")
    ap.add_argument("--har-betcity", help="офлайн-тест: HAR-файл Бетсити")
    ap.add_argument("--bc-now", type=float, default=0.0, help="офлайн-тест Бетсити: «текущее» время (unix) дампа")
    ap.add_argument("--ls-test", action="store_true", help="проверка Лиги Ставок: запросы без токенов, подробный вывод")
    ap.add_argument("--ls-set", action="store_true", help="записать заголовки x-api-cred и x-user Лиги Ставок в config.json")
    ap.add_argument("--har-olimp", metavar="ФАЙЛ", help="дамп Олимпа (браузер) для проверки без сети")
    ap.add_argument("--ma-test", action="store_true", help="проверка Марафона: страницы и коэффициенты")
    ap.add_argument("--ow-test", action="store_true", help="проверка 1win: список матчей и коэффициенты")
    ap.add_argument("--pm-test", action="store_true", help="проверка Polymarket: список матчей и цены")
    ap.add_argument("--bb-dump", action="store_true", help="диагностика БетБума: виды спорта и сырые данные киберспорта в ~/bb_dump.json")
    ap.add_argument("--olimp-test", action="store_true", help="проверка Олимпа: дерево, список матчей, страница матча")
    ap.add_argument("--ls-har", metavar="ФАЙЛ", help="взять x-api-cred и x-user Лиги Ставок из дампа браузера и записать в config.json")
    ap.add_argument("--har-ls", help="офлайн-тест: HAR-файл Лиги Ставок")
    ap.add_argument("--har-leon", help="офлайн-тест: HAR-файл Леона (с --bc-now — «текущее» время дампа)")
    ap.add_argument("--har-betboom", nargs="+", help="офлайн-тест: один или несколько HAR-файлов БетБума (WebSocket tree_ws)")
    ap.add_argument("--test-telegram", action="store_true", help="отправить тестовое сообщение и выйти")
    args = ap.parse_args()
    cfg = load_cfg(args.config)

    if args.probe:
        run_probe(cfg, args.probe)
        return
    if args.betcity_test:
        betcity_test(cfg)
        return
    if args.ma_test:
        marathon_test(cfg)
        return
    if args.ow_test:
        onewin_test(cfg)
        return
    if args.pm_test:
        polymarket_test(cfg)
        return
    if args.bb_dump:
        bb_dump(cfg)
        return
    if args.olimp_test:
        olimp_test(cfg)
        return
    if args.ls_test:
        ls_test(cfg)
        return
    if args.ls_set:
        ls_set(args)
        return
    if args.ls_har:
        ls_from_har(args)
        return
    if args.test_telegram:
        ok = tg_send(cfg, "✅ ArbPhone (%s): связь с Telegram работает" % esc(cfg["node"]))
        sys.exit(0 if ok else "Не отправлено: проверьте bot_token и chat_id")

    if cfg.get("role") == "worker":
        worker_main(cfg)
        return
    global USERS, PROMOS
    USERS = Users(cfg["users_file"] or os.path.join(os.path.dirname(os.path.abspath(__file__)), "users.json"))
    PROMOS = Promos(os.path.join(os.path.dirname(USERS.path), "promos.json"))
    if not (args.once or (args.har_fonbet and args.har_winline)):
        settings_restore(cfg)
        web_restore(cfg)
    if cfg["chat_id"]:
        USERS.add(cfg, cfg["chat_id"], "владелец")
    offline = bool(args.har_fonbet and args.har_winline)
    sent = {}
    if not (args.once or offline or args.no_send) and cfg["bot_token"] and cfg["chat_id"]:
        threading.Thread(target=bot_loop, args=(cfg,), daemon=True).start()
        log("меню-бот запущен: напишите боту /start")
    if not (args.once or offline):
        threading.Thread(target=settings_loop, args=(cfg,), daemon=True).start()
        threading.Thread(target=keepalive_loop, args=(cfg, keepalive_sites(cfg, [b for b in CL_BKS if cfg.get(b) and b not in (cfg.get("remote_bks") or [])])), daemon=True).start()
    idx = 0
    while True:
        t0 = time.time()
        try:
            CYC["start"] += 1
            idx = CYC["start"]
            run_cycle(cfg, args, sent)
        except KeyboardInterrupt:
            raise
        except Exception as e:
            log("ошибка цикла: %s: %s" % (type(e).__name__, e))
        if args.once or offline:
            break
        CYC["done"] = idx
        code_sync_safe(cfg, "main")
        heartbeat(cfg, cfg.get("node") or "main", "main", "парсит", {"info": re.sub(r"<[^>]+>", "", str(STORE.info))[:300]})
        REFRESH.wait(max(5.0, cfg["interval"] - (time.time() - t0)))
        REFRESH.clear()


if __name__ == "__main__":
    main()
