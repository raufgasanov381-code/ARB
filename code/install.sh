#!/data/data/com.termux/files/usr/bin/bash
# Установка телефона-работника ArbPhone (запускать в Termux одной командой)
REPO="raufgasanov381-code/ARB"; BR="data"
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
