#!/bin/bash
# Exhaustive check with sumcycle.c over all subsets containing 0 of every abelian group
# of odd order 3..31. Needs Linux, gcc (for unsigned __int128) and GNU time.
# Each summary line gives the group, its order, the number of subsets checked,
# fail (no ordering exists) and unknown (search stopped by its node/restart budget).
# sumcycle exits 0 when fail=0 even if unknown>0, so this script checks the summary
# line itself: a group counts as verified only if its line shows the full size range
# k=3..|G|, the expected number 2^(|G|-1)-|G| of subsets, fail=0 and unknown=0.
# Exit status: 0 all requested groups verified, 1 some group not verified, 2 setup error.
# Usage: bash run.sh [group ...]   e.g.  bash run.sh "3" "3 3"   (default: all 19 groups)
cd "$(dirname "$0")" || exit 2
unset KMIN KMAX LIMIT RESTARTS   # full subset-size range and default budgets
[ -x /usr/bin/time ] || { echo "GNU time (/usr/bin/time) is required"; exit 2; }
gcc -O2 -o sumcycle sumcycle.c || exit 2

check() {  # run one group, print its output, return 0 only if it is fully verified
  local out n=1 m
  for m in $1; do n=$((n * m)); done
  out=$(/usr/bin/time -f "%es" ./sumcycle $1 2>&1)
  printf '%s\n' "$out"
  printf '%s\n' "$out" | grep -qx "group $1 order=$n k=3\.\.$n subsets=$(( (1 << (n - 1)) - n )) fail=0 unknown=0 maxnodes=[0-9]* limit=[0-9]*"
}

# self-test: a run stopped by the budget must be rejected
if LIMIT=0 RESTARTS=0 check "3" > /dev/null; then
  echo "self-test failed: an inconclusive run was accepted"; exit 2
fi

if [ $# -eq 0 ]; then
  set -- "3" "5" "7" "9" "3 3" "11" "13" "15" "17" "19" "21" \
         "23" "25" "5 5" "27" "3 9" "3 3 3" "29" "31"
fi
status=0
for g in "$@"; do
  check "$g" || { echo "NOT VERIFIED: group $g"; status=1; }
done
[ $status -eq 0 ] && echo "ALL GROUPS VERIFIED (fail=0 unknown=0)"
exit $status
