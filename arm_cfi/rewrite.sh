#!/bin/sh

set -e
set -o pipefail

if [ $# -ne 2 ]; then
  echo "Usage: ${0##*/} <input binary> <output binary>"
  exit 1
fi

cd "$(dirname "$0")"
make
mkdir -p cfitmp
python src/dump.py "$1"
name="$(basename -- "$1")"
armv7l-unknown-linux-gnueabihf-objdump -d "$1" | grep 'bl.*__aeabi_read_tp' | cut -f1 -d':' | python src/format_lines.py "cfitmp/${name%.*}.lr"
src/rw "cfitmp/${name%.*}.bin" "cfitmp/${name%.*}.lr"
python src/join.py "$1" -o "$2"
