#!/bin/sh
# Usage: ./vd.sh push | build | pull | all
# push: local source -> VD:~/vsync ; build: lake build on VD ; pull: generated C -> ./c/
set -e
HOST=${VD_HOST:-VD}
RDIR=vsync
SSH="ssh -o LogLevel=ERROR"
push()  { rsync -az --delete -e "$SSH" --exclude .lake --exclude c --exclude build-local ./ "$HOST:$RDIR/"; }
build() { $SSH "$HOST" "cd $RDIR && PATH=\$HOME/.elan/bin:\$PATH timeout 300 lake build VSync +Main 2>&1"; }
pull()  { mkdir -p c && rsync -az --delete -e "$SSH" "$HOST:$RDIR/.lake/build/ir/" c/; }
case "${1:-all}" in
  push) push;; build) build;; pull) pull;;
  all) push; build; pull;;
  *) echo "usage: $0 push|build|pull|all" >&2; exit 1;;
esac
