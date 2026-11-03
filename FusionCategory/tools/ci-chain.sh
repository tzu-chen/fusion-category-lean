#!/bin/sh
# FusionCategory/tools/ci-chain.sh -- run the CI gate chain locally.
#
# Mirrors `.github/workflows/fusion-category-ci.yml` from the "Fetch the pinned
# Mathlib oleans" step onwards, in the same order, so that the workflow can be
# verified without GitHub.  It deliberately does not do the three things the
# workflow does before the chain: check out a fresh clone, install elan, install
# the toolchain pinned by lean-toolchain.  For "fresh clone + fresh cache" use
# the clean-build script (batch item B1); this script is the chain of gates.
#
# Deliberate differences from CI:
#   * CI stops at the first red gate (a step's non-zero exit fails the job).
#     Here every gate runs and a summary is printed, so one run reports every
#     defect; the exit status is 1 if any gate failed.
#   * `lake exe cache get` is skipped unless --cache-get is given (or
#     CI_CHAIN_CACHE_GET=1): on a warm tree it downloads nothing, and its job in
#     CI is to populate a fresh tree.
#
# Usage: sh tools/ci-chain.sh [--cache-get] [--audit-out FILE]
# Exit:  0 if every gate passed, 1 otherwise.

set -u
cd "$(dirname "$0")/.." || exit 2

cache_get=0
audit_out=.scratch/ci-audit-output.txt
while [ $# -gt 0 ]; do
  case "$1" in
    --cache-get) cache_get=1; shift ;;
    --audit-out) audit_out=$2; shift 2 ;;
    -h|--help) sed -n '2,20p' "$0"; exit 0 ;;
    *) echo "ci-chain: unknown argument: $1" >&2; exit 2 ;;
  esac
done
[ "${CI_CHAIN_CACHE_GET:-0}" = "1" ] && cache_get=1
mkdir -p "$(dirname "$audit_out")"

gates=0
fail=0
failed=""

# run_gate NAME SHELL-FUNCTION-OR-COMMAND...
run_gate() {
  name=$1; shift
  gates=$((gates + 1))
  printf '\n===== gate: %s =====\n' "$name"
  start=$(date +%s)
  if "$@"; then
    printf '===== gate: %s -- PASS (%ss)\n' "$name" "$(( $(date +%s) - start ))"
  else
    printf '===== gate: %s -- FAIL (%ss)\n' "$name" "$(( $(date +%s) - start ))"
    fail=1
    failed="${failed}  - ${name}
"
  fi
}

# Capture the audit output, and fail on a Lean error exactly as the workflow
# step does (there it is `lake env lean AxiomAudit.lean | tee`).
audit_capture() {
  if lake env lean AxiomAudit.lean > "$audit_out" 2>&1; then
    printf 'audit output written to %s (%s non-blank lines)\n' \
      "$audit_out" "$(grep -c . "$audit_out" || true)"
  else
    echo "AxiomAudit.lean failed to elaborate; its output follows:" >&2
    cat "$audit_out" >&2
    return 1
  fi
}

# The chain must leave the tracked tree alone.
tree_clean() {
  root=$(git -C .. rev-parse --show-toplevel 2>/dev/null) || return 0
  status=$(git -C "$root" status --porcelain)
  if [ -n "$status" ]; then
    echo "the chain modified tracked files:" >&2
    echo "$status" >&2
    return 1
  fi
  echo "tracked tree clean after the chain"
}

if [ "$cache_get" = 1 ]; then
  run_gate "fetch the pinned Mathlib oleans (lake exe cache get)" lake exe cache get
fi

# Gate: the package builds from source with the pinned toolchain and Mathlib.
run_gate "clean build (lake build)" lake build

# Gate: every module of the library compiles.  `lake build` honours
# defaultTargets = ["FusionCategory"], i.e. the umbrella's import closure, so the
# three FusionCategory/MathlibPatches* modules are outside it; the module list is
# derived from the work tree, never hand-written.
build_all_modules() {
  modules=$(git -C .. ls-files 'FusionCategory/FusionCategory/*.lean' \
    | sed -e 's#^FusionCategory/##' -e 's#\.lean$##' -e 's#/#.#g')
  if [ -z "$modules" ]; then echo "no modules found" >&2; return 1; fi
  # A module name never ends in ".lean": Lake would accept such a target and
  # hide a broken sed in this very step.
  case "$modules" in
    *".lean"*) echo "module-name derivation failed: a name ends in .lean" >&2; return 1 ;;
  esac
  printf 'library modules to build: %s\n' "$(printf '%s\n' "$modules" | wc -l)"
  # Word splitting is intended below: the words are Lean module names, which
  # cannot contain spaces or glob characters.
  # shellcheck disable=SC2086
  lake build $modules
}
run_gate "every library module compiles (not only the umbrella closure)" build_all_modules

# Evidence, and a gate in its own right: a Lean error fails here too.
run_gate "audit output (lake env lean AxiomAudit.lean)" audit_capture

# Gate 4: the enforcing axiom audit against tools/audit-manifest.txt.
run_gate "Gate 4 (tools/audit-gate.sh)" sh tools/audit-gate.sh

# Gate 4 self-test: the gate must fail on every fixture that must fail.
run_gate "Gate 4 self-test (tools/selftest/run.sh)" sh tools/selftest/run.sh

if git -C .. rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  run_gate "tracked tree clean" tree_clean
else
  printf '\n(not a git work tree: the tracked-tree-clean gate is skipped)\n'
fi

printf '\n===== summary: %s gate(s) =====\n' "$gates"
if [ "$fail" -ne 0 ]; then
  printf 'failed gates:\n%s' "$failed"
  echo "ci-chain: the workflow chain is RED"
  exit 1
fi
echo "ci-chain: the workflow chain is green"
