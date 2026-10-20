#!/usr/bin/env bash
# Run a `metrics` command over a project in parallel shards and wait for all of them.
#
#   bash run.sh PROJECT OUT_DIR [SHARDS] [dump|replace|leak] [extra arguments...]
#
# PROJECT is the root of the measured project, built (`lake build`) with the same toolchain as this
# tool. The command defaults to `dump`, with full records for Numlib and NumlibSurface, full records
# for one Mathlib module in four (the baseline) and statement hashes for the rest of Mathlib.
# `replace` and `leak` get `--roots Numlib,NumlibSurface` and the extra arguments. Each shard
# imports the whole project (3 to 8 GB resident); if the project has `scripts/lbuild.sh`, each
# shard takes a build slot through it.
set -u
HERE=$(cd "$(dirname "$0")" && (pwd -W 2>/dev/null || pwd))
PROJECT=$(cd "$1" && (pwd -W 2>/dev/null || pwd)) || exit 1
OUT=$2; SHARDS=${3:-4}; shift 3 2>/dev/null || shift $#
CMD=dump
case "${1:-}" in dump|replace|leak) CMD=$1; shift ;; esac
if [ "$CMD" = dump ]; then
  set -- --roots Numlib,NumlibSurface --full Numlib,NumlibSurface,Mathlib --sample 4 --stmt Mathlib "$@"
else
  set -- --roots Numlib,NumlibSurface "$@"
fi
EXE="$HERE/.lake/build/bin/metrics.exe"
[ -f "$EXE" ] || EXE="$HERE/.lake/build/bin/metrics"
[ -f "$EXE" ] || { echo "build the tool first: (cd $HERE && lake build)" >&2; exit 1; }
SLOT=()
[ -f "$PROJECT/scripts/lbuild.sh" ] && SLOT=(bash "$PROJECT/scripts/lbuild.sh")
mkdir -p "$OUT"
OUT=$(cd "$OUT" && (pwd -W 2>/dev/null || pwd))
cd "$PROJECT" || exit 1
pids=()
for i in $(seq 0 $((SHARDS - 1))); do
  "${SLOT[@]}" lake env "$EXE" "$CMD" "$@" --shard "$i/$SHARDS" --out "$OUT" > "$OUT/run.$i.log" 2>&1 &
  pids+=($!)
done
rc=0
for p in "${pids[@]}"; do wait "$p" || rc=1; done
tail -q -n 1 "$OUT"/run.*.log
exit $rc
