#!/bin/sh
# FusionCategory/tools/clean-build.sh -- B1 / WP0 Task 0.2: reproduce the clean build.
#
# A clean build is a fresh clone, a fresh Mathlib cache, and no LEAN_PATH
# override.  This script performs exactly that and fails if any step fails:
#
#   1. git clone <SRC> and check out <REV>              (fresh tree; no .lake)
#   2. lake exe cache get                               (fresh cache if FRESH_CACHE=1)
#   3. lake build                                       (must say "Build completed successfully")
#   4. lake env lean AxiomAudit.lean                    (the raw audit; no errors)
#   5. sh tools/audit-gate.sh                           (Gate 4, enforcing)
#   6. sh tools/selftest/run.sh                         (the gate must be seen to fail)
#
# Every lake/lean invocation runs with LEAN_PATH *removed* from the environment,
# so an inherited override (the reason the "green build" was not reproducible
# before) cannot silently satisfy an import.
#
# Usage (from anywhere):
#   sh FusionCategory/tools/clean-build.sh
#
# Environment:
#   SRC           clone source   (default: https://github.com/tzu-chen/fusion-category-lean.git;
#                                 a file:// URL of a local checkout also works)
#   REV           commit to build (default: the tip of SRC's default branch)
#   BUILD_ROOT    where the tree and logs go (default: $PWD/.clean-build)
#   FRESH_CACHE=1 use a Mathlib cache inside BUILD_ROOT instead of the shared
#                 $HOME/.cache/mathlib: this is the only way to observe the
#                 download, and therefore the only evidence that the cache step
#                 works from nothing (costs the full download).
#   KEEP=0        delete the built tree afterwards (default 1: keep it, ~7.7 GB)
#
# Exit status: 0 only if all six steps passed.
set -eu

SRC=${SRC:-https://github.com/tzu-chen/fusion-category-lean.git}
BUILD_ROOT=${BUILD_ROOT:-$PWD/.clean-build}
TREE=$BUILD_ROOT/fusion-category-lean
LOGS=$BUILD_ROOT/logs
CACHE_NOTE=shared
if [ "${FRESH_CACHE:-0}" = "1" ]; then
  MATHLIB_CACHE_DIR=$BUILD_ROOT/mathlib-cache
  export MATHLIB_CACHE_DIR
  CACHE_NOTE="fresh ($MATHLIB_CACHE_DIR)"
else
  CACHE_NOTE="shared (${MATHLIB_CACHE_DIR:-${XDG_CACHE_HOME:-$HOME/.cache}/mathlib})"
fi

say() { printf '%s\n' "$*"; }
die() { printf 'CLEAN-BUILD FAILED: %s\n' "$*" >&2; exit 1; }
size() { du -sk "$1" 2>/dev/null | cut -f1 || echo 0; }

rm -rf "$TREE" "$LOGS"
mkdir -p "$LOGS"
say "clean-build: SRC=$SRC"
say "clean-build: BUILD_ROOT=$BUILD_ROOT"
say "clean-build: Mathlib cache: $CACHE_NOTE"
say "toolchain: $(lean --version)"
say "lake     : $(lake --version)"
say "inherited LEAN_PATH (removed for every step): ${LEAN_PATH:-<unset>}"

# --- 1. fresh tree --------------------------------------------------------
t0=$(date -u +%s)
git clone --quiet "$SRC" "$TREE" || die "git clone $SRC"
if [ -n "${REV:-}" ]; then git -C "$TREE" checkout --quiet "$REV" || die "checkout $REV"; fi
HEAD=$(git -C "$TREE" rev-parse HEAD)
[ -z "$(git -C "$TREE" status --porcelain)" ] || die "fresh clone is not a clean tree"
[ ! -d "$TREE/FusionCategory/.lake" ] || die "fresh clone already contains .lake -- not a clean build"
say "step 1: cloned $HEAD (clean tree, no .lake) in $(( $(date -u +%s) - t0 ))s"

# The reproducibility claim is about a named toolchain: refuse to build with
# another one.  (On a machine with elan, `lean` is the shim and already honours
# lean-toolchain; on a bare image this is the only check there is.)
WANT=$(sed -n 's|.*leanprover/lean4:v\{0,1\}\([0-9][0-9.]*\).*|\1|p' "$TREE/FusionCategory/lean-toolchain")
GOT=$(lean --version | sed -n 's/.*version \([0-9][0-9.]*\).*/\1/p')
if [ -n "$WANT" ] && [ "$WANT" != "$GOT" ]; then
  if [ "${ALLOW_TOOLCHAIN_MISMATCH:-0}" = "1" ]; then
    say "step 1: WARNING lean-toolchain wants $WANT, lean is $GOT (allowed by ALLOW_TOOLCHAIN_MISMATCH=1)"
  else
    die "lean-toolchain wants $WANT but lean is $GOT (set ALLOW_TOOLCHAIN_MISMATCH=1 to build anyway)"
  fi
else
  say "step 1: toolchain $GOT matches lean-toolchain"
fi

cd "$TREE/FusionCategory"

# --- 2. Mathlib cache -----------------------------------------------------
c0=$(size "${MATHLIB_CACHE_DIR:-${XDG_CACHE_HOME:-$HOME/.cache}/mathlib}")
t0=$(date -u +%s)
env -u LEAN_PATH lake exe cache get > "$LOGS/cache-get.log" 2>&1 || { tail -20 "$LOGS/cache-get.log"; die "lake exe cache get"; }
t1=$(date -u +%s)
c1=$(size "${MATHLIB_CACHE_DIR:-${XDG_CACHE_HOME:-$HOME/.cache}/mathlib}")
say "step 2: cache get in $((t1-t0))s; cache dir grew by $((c1-c0)) KiB to $((c1)) KiB"
grep -E 'No files to download|Decompressing|Completed successfully' "$LOGS/cache-get.log" | tail -3 || true
if grep -q 'No files to download' "$LOGS/cache-get.log" && [ "$((c1-c0))" -lt 1024 ]; then
  say "step 2: NOTE the cache already held every artifact -- this run did not exercise the download"
fi

# --- 3. lake build --------------------------------------------------------
t0=$(date -u +%s)
env -u LEAN_PATH lake build > "$LOGS/build.log" 2>&1 || { tail -40 "$LOGS/build.log"; die "lake build"; }
t1=$(date -u +%s)
grep -q 'Build completed successfully' "$LOGS/build.log" || die "lake build printed no success line"
if grep -qE '^error' "$LOGS/build.log"; then die "lake build printed an error line"; fi
JOBS=$(sed -n 's/.*Build completed successfully (\([0-9]*\) jobs).*/\1/p' "$LOGS/build.log" | tail -1)
WARN=$(grep -cE '^warning' "$LOGS/build.log" || true)
say "step 3: lake build ok ($JOBS jobs, $WARN warning lines) in $((t1-t0))s"

# --- 4. the raw audit -----------------------------------------------------
t0=$(date -u +%s)
env -u LEAN_PATH lake env lean AxiomAudit.lean > "$LOGS/audit-raw.log" 2>&1 || { tail -40 "$LOGS/audit-raw.log"; die "AxiomAudit.lean"; }
if grep -qE 'error[:(]' "$LOGS/audit-raw.log"; then die "AxiomAudit.lean printed an error"; fi
NAUD=$(grep -cE 'does not depend on any axioms|depends on axioms' "$LOGS/audit-raw.log" || true)
say "step 4: AxiomAudit.lean ok, $NAUD audited declarations in $(( $(date -u +%s) - t0 ))s"

# --- 5. Gate 4 ------------------------------------------------------------
t0=$(date -u +%s)
env -u LEAN_PATH sh tools/audit-gate.sh > "$LOGS/gate.log" 2>&1 || { tail -30 "$LOGS/gate.log"; die "audit-gate.sh (Gate 4 red)"; }
grep -q 'gate 4: all audited declarations within budget' "$LOGS/gate.log" || die "gate printed no verdict"
say "step 5: Gate 4 green in $(( $(date -u +%s) - t0 ))s"

# --- 6. the gate's own self-test -----------------------------------------
t0=$(date -u +%s)
env -u LEAN_PATH sh tools/selftest/run.sh > "$LOGS/selftest.log" 2>&1 || { tail -30 "$LOGS/selftest.log"; die "selftest (the gate did not behave)"; }
grep -q 'selftest: every fixture behaved as required' "$LOGS/selftest.log" || die "selftest printed no verdict"
say "step 6: selftest ok ($(grep -c 'selftest: ok' "$LOGS/selftest.log") fixtures) in $(( $(date -u +%s) - t0 ))s"

say "clean-build: REPRODUCED  (commit $HEAD, $JOBS jobs, $NAUD audited declarations)"

if [ "${KEEP:-1}" = "0" ]; then
  cd "$BUILD_ROOT"
  rm -rf "$TREE"
  if [ "${FRESH_CACHE:-0}" = "1" ]; then rm -rf "$BUILD_ROOT/mathlib-cache"; fi
  say "clean-build: tree removed (KEEP=0); logs kept in $LOGS"
fi
