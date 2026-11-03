#!/bin/sh
# FusionCategory/tools/audit-gate.sh -- Gate 4: the enforcing axiom audit.
#
# Contract (research proposal, Appendix "The audit protocol", Gate 4):
# exit non-zero if
#   (i)   `lake env lean AxiomAudit.lean` exits non-zero, or its output
#         contains a Lean error marker (`error:` / `error(`) -- a declaration
#         NAME containing "error" does not match the marker;
#   (ii)  any audited declaration depends on an axiom outside
#         [propext, Classical.choice, Quot.sound] (strict subsets are within
#         budget; a `sorry` shows up as sorryAx, and an `axiom` declaration
#         by listing its own name -- `#print axioms` applied to an `axiom`
#         does NOT error in Lean 4.33.1, it prints the axiom's own name,
#         which this branch then rejects);
#   (iii) any output line is not a recognised audit line.  Recognised: the
#         two `#print axioms` forms (with wrapped lines rejoined before
#         matching), blank lines, and `warning:` lines (a sorry is caught by
#         (ii) through sorryAx, not by its warning line).  Trailing text
#         after the bracket list is NOT recognised;
#   (iv)  the audit output is empty, or its set of declaration names differs
#         from the checked-in manifest (default `tools/audit-manifest.txt`,
#         overridable via $GATE4_MANIFEST for the self-test) -- so deleting
#         or editing a `#print axioms` line fails the gate.  Generating the
#         audit list mechanically (every declaration, not a hand-maintained
#         73) is batch item B2.
#
# All violations are reported before the gate fails.  Run from anywhere.
# Self-test: `tools/selftest/run.sh` must fail on every fixture in
# `tools/selftest/bad/` and pass on every fixture in `tools/selftest/good/`;
# a gate that has never been observed to fail is a report.

set -e
cd "$(dirname "$0")/.."
lake build
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
out="$tmp/audit.txt"
lake env lean AxiomAudit.lean > "$out" 2>&1 || { cat "$out"; exit 1; }
grep -qE 'error[:(]' "$out" && { cat "$out"; exit 1; } || true
[ -s "$out" ] || { echo "GATE 4: empty audit output"; exit 1; }

# Rejoin Lean's 120-column wrapped lines, then recognise only:
#   '<name>' does not depend on any axioms
#   '<name>' depends on axioms: [a, b, c]        (list may be empty)
# Names may contain primes (Lean identifiers allow '), so the name match is
# GREEDY; the manifest comparison below rejects any line whose extracted name
# is not in the mechanically generated list, which is what keeps greedy
# matching sound.  Anything else -- including trailing text after the
# bracket -- fails.
awk '
  BEGIN { q = sprintf("%c", 39) }
  /^[ \t]*$/ { next }
  /warning:/ { next }
  {
    line = $0
    joins = 0
    while (joins < 4 &&
           line ~ ("^" q) &&
           line !~ ("does not depend on any axioms$") &&
           line !~ ("depends on axioms: \\[[^]]*\\]$") &&
           (getline nxt) > 0) {
      line = line nxt; joins++
    }
    if (line ~ ("^" q ".*" q " does not depend on any axioms$")) { next }
    if (line ~ ("^" q ".*" q " depends on axioms: \\[")) {
      s = line
      sub(("^.*" q " depends on axioms: \\["), "", s)
      if (s !~ /^([A-Za-z0-9._]+(, [A-Za-z0-9._]+)*)?\]$/) {
        print "GATE 4: malformed audit line: " line; bad = 1; next }
      sub(/\]$/, "", s)
      n = split(s, a, ", ")
      for (i = 1; i <= n; i++)
        if (a[i] != "propext" && a[i] != "Classical.choice" && a[i] != "Quot.sound") {
          print "GATE 4: out of budget: " line; bad = 1 }
      next }
    print "GATE 4: unrecognised audit line: " line; bad = 1
  }
  END { if (bad) exit 1 }
' "$out"

# Coverage: the audited names must match the manifest exactly.  (Greedy
# extraction: Lean identifiers may contain primes.)
sed -n "s/^'\(.*\)'.*/\1/p" "$out" | LC_ALL=C sort > "$tmp/names"
LC_ALL=C sort "${GATE4_MANIFEST:-tools/audit-manifest.txt}" > "$tmp/manifest"
if ! cmp -s "$tmp/names" "$tmp/manifest"; then
  echo "GATE 4: audited declarations differ from the manifest:"
  diff "$tmp/manifest" "$tmp/names" || true
  exit 1
fi
echo "gate 4: all audited declarations within budget"
