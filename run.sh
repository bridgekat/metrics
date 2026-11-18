#!/usr/bin/env bash
# Run one declaration dump per shard inside the measured project's Lake environment.
set -eu
if (( $# < 2 )); then
  echo "usage: run.sh PROJECT OUT [SHARDS] [dump] [dump options...]" >&2
  exit 2
fi
abspath() { (cd "$1" && (pwd -W 2>/dev/null || pwd)); }
here=$(abspath "$(dirname "$0")")
project=$(abspath "$1")
mkdir -p "$2"
out=$(abspath "$2")
shift 2
shards=1
if [[ ${1:-} =~ ^[0-9]+$ ]]; then shards=$1; shift; fi
[[ $shards =~ ^[1-9][0-9]*$ ]] || { echo "invalid shard count" >&2; exit 2; }
if [[ ${1:-} == dump ]]; then shift; fi
exe="$here/.lake/build/bin/metrics"
[[ ! -f "$exe.exe" ]] || exe="$exe.exe"
[[ -f "$exe" ]] || { echo "build the metrics executable with lake build" >&2; exit 1; }
slot=()
[[ ! -f "$project/scripts/lbuild.sh" ]] || slot=(bash "$project/scripts/lbuild.sh")
cd "$project"
pids=()
for ((i=0; i<shards; i++)); do
  "${slot[@]}" lake env "$exe" dump --roots Numlib,NumlibSurface "$@" --shard "$i/$shards" --out "$out" >"$out/run.$i.log" 2>&1 &
  pids+=($!)
done
rc=0
for pid in "${pids[@]}"; do wait "$pid" || rc=1; done
exit "$rc"
