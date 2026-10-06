#!/bin/bash
# Elaboration times of the declarations of the test files, as reported in the paper
# (Section 7). Run from the root of the repository, after `lake build KernelHomTests`:
#   KernelHomTests/timings.sh [number of runs, default 5]
# Each file is elaborated sequentially (`Elab.async=false`) with `trace.profiler`, its imports being
# already built; the time of a declaration is the time of its whole command (statement and proof).
# The docstrings are removed from a temporary copy of each file, so that the profiler prints the
# names of the declarations. The script prints, for each declaration, the median, minimum and
# maximum over the runs. It needs perl and python3.
set -e
RUNS=${1:-5}
TMP=$(mktemp -d)
for f in Examples Basu; do
  perl -0pe 's{/--.*?-/\n}{}gs' "KernelHomTests/$f.lean" > "$TMP/$f.lean"
  for i in $(seq 1 "$RUNS"); do
    lake env lean -Dtrace.profiler=true -Dtrace.profiler.threshold=1 -DElab.async=false \
      "$TMP/$f.lean" 2>/dev/null \
      | grep -E '^\[Elab\.command\] \[[0-9.]+\] ✅️ (theorem|lemma) ' >> "$TMP/$f.txt" || true
  done
done
python3 - "$TMP" "$RUNS" <<'EOF'
import collections, re, statistics, sys
tmp, runs = sys.argv[1], int(sys.argv[2])
for f in ["Examples", "Basu"]:
    times = collections.defaultdict(list)
    order = []
    for line in open(f"{tmp}/{f}.txt"):
        m = re.match(r"^\[Elab\.command\] \[([0-9.]+)\] ✅️ (theorem|lemma) ([^\s]+)", line)
        # A `lemma` is elaborated as a `theorem`: keep the `theorem` line only.
        if m and m.group(2) == "theorem":
            if m.group(3) not in times:
                order.append(m.group(3))
            times[m.group(3)].append(float(m.group(1)))
    print(f"== KernelHomTests/{f}.lean ({runs} runs)")
    for name in order:
        v = times[name]
        print(f"{name:32.32s} median {1000 * statistics.median(v):6.0f} ms"
              f"  (min {1000 * min(v):.0f}, max {1000 * max(v):.0f})")
EOF
rm -rf "$TMP"
