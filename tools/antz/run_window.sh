#!/bin/bash
# Usage: tools/antz/run_window.sh <name> <sagefile>
# Opens a tmux window <name> in session dpnm running an interactive Sage REPL
# (needed for Magma to initialize), logs it to logs/<name>.log and loads <sagefile>.
cd ~/darmonpoints-nomagma
mkdir -p logs
tmux new-window -t dpnm -n "$1" -c ~/darmonpoints-nomagma
tmux pipe-pane -o -t "dpnm:$1" "cat >> ~/darmonpoints-nomagma/logs/$1.log"
tmux send-keys -t "dpnm:$1" "export PYTHONPATH=\$HOME/darmonpoints-nomagma; ~/miniforge3/envs/darmonpoints-dev/bin/sage --simple-prompt" Enter
sleep 20
tmux send-keys -t "dpnm:$1" "load(\"$2\")" Enter
