#!/bin/bash
# Usage: tools/antz/run_sage_window.sh <name> "<sage statements>"
# Like run_window.sh but sends arbitrary statements to the REPL.
cd ~/darmonpoints-nomagma
mkdir -p logs
tmux new-window -t dpnm -n "$1" -c ~/darmonpoints-nomagma
tmux pipe-pane -o -t "dpnm:$1" "cat >> ~/darmonpoints-nomagma/logs/$1.log"
tmux send-keys -t "dpnm:$1" "export PYTHONPATH=\$HOME/darmonpoints-nomagma; ~/miniforge3/envs/darmonpoints-dev/bin/sage --simple-prompt" Enter
sleep 20
tmux send-keys -t "dpnm:$1" "$2" Enter
