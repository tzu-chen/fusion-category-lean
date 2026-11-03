#!/bin/sh
# FusionCategory/tools/gen-audit.sh -- Gate 4, batch item B2 (a).
#
# MECHANICAL generation of the axiom-audit list: no hand-maintained name list
# anywhere in the chain.  From the elaborated environment it writes
#
#   $OUT/tools/audit-list.tsv       <name> <TAB> <kind> <TAB> <declaring module>
#   $OUT/tools/audit-manifest.txt   the names alone (the gate's coverage input)
#   $OUT/$AUDIT_FILE                the audit file: one `#print axioms <name>` per name
#
# and then checks that nothing escaped.  Three guards, in this order:
#
#   staleness.  An olean older than its source would make the audit report on
#   code that is not in the tree -- the exact kind of silent hole this batch is
#   about.  The script lists the stale modules of the import closure and stops
#   (exit 2, like every other refusal).  `AUDIT_REBUILD_STALE=1` recompiles exactly those modules from
#   source with `lean -o` into a private mirror of the olean tree and audits
#   that instead; `AUDIT_ALLOW_STALE=1` only warns.
#
#   coverage.  The audit sees the *built surface*, the import closure of the
#   library root `FusionCategory.lean`.  Any source module of the library
#   outside that closure that declares a constant would be a hole.  The script
#   compiles those "pariah" modules with `lean -o` into a private LEAN_PATH,
#   re-runs the enumeration over them alone, and fails (exit 3) if the pariah
#   pass yields any name the main pass does not.
#
#   budget.  Left to the gate itself (`tools/audit-gate.sh`), never decided here.
#
# Configuration (all optional; the defaults are the in-tree ones):
#   OUT                 where the generated files go   (default: the package dir)
#   AUDIT_FILE          name of the generated audit file
#                       (default: AxiomAuditGenerated.lean; landing uses
#                        `OUT=. AUDIT_FILE=AxiomAudit.lean`)
#   AUDIT_ROOT          the dir holding `FusionCategory.lean` and `FusionCategory/`
#                       (default: the package dir)
#   AUDIT_OLEANS        the package's olean dir
#                       (default: <package>/.lake/build/lib/lean)
#   AUDIT_REBUILD_STALE=1   recompile stale modules instead of stopping
#   AUDIT_ALLOW_STALE=1     audit the stale oleans with a warning
#   AUDIT_SKIP_PARIAH=1     skip the coverage guard (reported as skipped)
#   AUDIT_KEEP_WORK=1       keep the private olean mirrors under $OUT/tools/work
#
# Determinism: no timestamps, no host names, no iteration-order dependence (the
# enumeration is sorted in Lean and again with `LC_ALL=C`), so a re-run on the
# same oleans reproduces the three generated files byte for byte.
set -e
cd "$(dirname "$0")/.."
PKG=$PWD
OUT=${OUT:-$PKG}
AUDIT_FILE=${AUDIT_FILE:-AxiomAuditGenerated.lean}
AUDIT_ROOT=${AUDIT_ROOT:-$PKG}
AUDIT_OLEANS=${AUDIT_OLEANS:-$PKG/.lake/build/lib/lean}
LEAN=${LEAN:-lean}
TAB=$(printf '\t')
say() { echo "gen-audit: $*"; }
die() { echo "gen-audit: $*" >&2; exit 2; }
# Everything is configured by environment variable; a positional argument is
# always a mistake (`sh tools/gen-audit.sh OUT=.` does not set OUT).
[ $# -eq 0 ] || die "unexpected argument(s): $*  (configuration is by environment variable -- see the header)"

# absolute paths: `lean -o` and `cp -rs` need them
case $AUDIT_OLEANS in /*) ;; *) AUDIT_OLEANS=$PKG/$AUDIT_OLEANS ;; esac
case $AUDIT_ROOT   in /*) ;; *) AUDIT_ROOT=$PKG/$AUDIT_ROOT ;; esac
[ -f "$AUDIT_ROOT/FusionCategory.lean" ] ||
  die "no library root at $AUDIT_ROOT/FusionCategory.lean"
[ -d "$AUDIT_OLEANS/FusionCategory" ] ||
  die "no package oleans under $AUDIT_OLEANS -- build first"
mkdir -p "$OUT/tools"

if [ "${AUDIT_KEEP_WORK:-0}" = 1 ]; then WORK=$OUT/tools/work; rm -rf "$WORK"; mkdir -p "$WORK";
else WORK=$(mktemp -d); trap 'rm -rf "$WORK"' EXIT; fi

# module name -> source file / olean file
src_of()   { echo "$AUDIT_ROOT/$(echo "$1" | tr . /).lean"; }
olean_of() { echo "$AUDIT_OLEANS/$(echo "$1" | tr . /).olean"; }
pkg_imports() { sed -n 's/^import \(FusionCategory[A-Za-z0-9_.]*\).*/\1/p' "$(src_of "$1")"; }

# compile_mirror <mirror dir> <module>...  -- compile the modules from source,
# in dependency order, into a copy-on-write mirror of the olean tree.  The
# mirror is needed because the olean search (`SearchPath.findWithExt`) matches
# on the *root* component of a module name only: a search-path root that merely
# adds `FusionCategory/...` shadows every other module of that root.
compile_mirror() {
  dest=$1; shift
  rm -rf "$dest"; mkdir -p "$dest"
  cp -rs "$AUDIT_OLEANS/." "$dest/"
  pending=$*
  guard=0
  while [ -n "$pending" ]; do
    guard=$((guard + 1))
    [ "$guard" -le 60 ] || die "module compilation did not converge: $pending"
    progressed=0
    for m in $pending; do
      missing=0
      for dep in $(pkg_imports "$m"); do
        case " $pending " in *" $dep "*) missing=1 ;; esac
      done
      [ "$missing" = 1 ] && continue
      dst=$dest/$(echo "$m" | tr . /); mkdir -p "$(dirname "$dst")"
      src=$(src_of "$m")
      say "compiling $m from source"
      # `lean -o` insists the input is under the root directory: run there.
      ( cd "$AUDIT_ROOT" &&
        LEAN_PATH="$dest:$AUDIT_OLEANS${LEAN_PATH:+:$LEAN_PATH}" \
        "$LEAN" -o "$dst.olean" -i "$dst.ilean" "${src#$AUDIT_ROOT/}" )
      progressed=1
      pending=$(echo "$pending" | tr ' ' '\n' | sed "/^$m\$/d" | sed '/^$/d' | tr '\n' ' ')
    done
    [ "$progressed" = 1 ] || die "dependency cycle: $pending"
  done
}

# ---------------------------------- 0. what "the library" is, from the sources
# transitive closure of `import FusionCategory...` from the library root
closure=$WORK/closure
work=$WORK/pending-modules
pariahs=$WORK/modules
echo FusionCategory > "$work"
seen=""
while [ -s "$work" ]; do
  m=$(head -1 "$work"); sed -i 1d "$work"
  case " $seen " in *" $m "*) continue ;; esac
  seen="$seen $m"
  [ -f "$(src_of "$m")" ] || continue
  pkg_imports "$m" >> "$work"
done
printf '%s\n' $seen | LC_ALL=C sort > "$closure"
find "$AUDIT_ROOT/FusionCategory" -name '*.lean' |
  sed "s|^$AUDIT_ROOT/||; s|\.lean$||; s|/|.|g" | LC_ALL=C sort > "$pariahs"
LC_ALL=C comm -23 "$pariahs" "$closure" > "$pariahs.only"
pariah_count=$(wc -l < "$pariahs.only" | tr -d ' ')
say "library root import closure: $(wc -l < "$closure" | tr -d ' ') modules; outside it: $pariah_count"
sed 's/^/gen-audit:   outside the closure: /' "$pariahs.only"

# ----------------------------------------------------- 1. the staleness guard
stale=""
for m in $(cat "$closure"); do
  [ -f "$(src_of "$m")" ] || continue
  # `-nt` is true when the second file is missing, so a module with no olean counts
  [ "$(src_of "$m")" -nt "$(olean_of "$m")" ] && stale="$stale $m"
done
stale=$(echo $stale)
if [ -n "$stale" ]; then
  say "STALE OLEANS -- olean older than source for: $stale"
  if [ "${AUDIT_REBUILD_STALE:-0}" = 1 ]; then
    compile_mirror "$WORK/rebuilt" $stale
    AUDIT_OLEANS=$WORK/rebuilt
    say "auditing the freshly compiled modules instead"
  elif [ "${AUDIT_ALLOW_STALE:-0}" = 1 ]; then
    say "AUDIT_ALLOW_STALE=1: auditing stale oleans anyway (the report describes code that is not in the tree)"
  else
    die "refusing to audit stale oleans; re-run with AUDIT_REBUILD_STALE=1 to recompile them from source"
  fi
fi

# ---------------------------------------------------------------- 2. the list
say "enumerating the environment"
LEAN_PATH="$AUDIT_OLEANS${LEAN_PATH:+:$LEAN_PATH}" \
  "$LEAN" "$PKG/tools/AuditList.lean" > "$OUT/tools/audit-list.tsv"
[ -s "$OUT/tools/audit-list.tsv" ] || die "empty enumeration"

# sort by module then name for the audit file; the manifest is the names alone
LC_ALL=C sort -t"$TAB" -k3,3 -k1,1 "$OUT/tools/audit-list.tsv" > "$OUT/tools/audit-list.by-module.tsv"
cut -f1 "$OUT/tools/audit-list.by-module.tsv" | LC_ALL=C sort > "$OUT/tools/audit-manifest.txt"

# ------------------------------------------------- 3. the audit file itself
{
  cat <<'HDR'
import FusionCategory

-- The list is every constant the package declares, compiler-generated
-- `match_1`-style auxiliaries included: excluding them would need exactly the
-- hand-maintained exclusion list that B2 exists to remove.  The `auxLemma`
-- linter objects to *referencing* such a name (they are unstable across
-- refactors); here the reference is regenerated with the name, and the audit's
-- subject is axiom dependence, not name stability.  Its second output line
-- (`Note: ...`) is also the only thing in the output the gate cannot recognise.
set_option linter.auxLemma false

/-!
# Axiom audit -- ENO 8.23 (GENERATED FILE -- do not edit)

Generated by `tools/gen-audit.sh` from `tools/AuditList.lean`, which walks the
elaborated environment of `import FusionCategory` and emits one `#print axioms`
line for every constant declared by a module of the package.  Regenerate with

    sh tools/gen-audit.sh OUT=. AUDIT_FILE=AxiomAudit.lean

and check it with `sh tools/audit-gate.sh` (manifest `tools/audit-manifest.txt`,
regenerated by the same command).

Axiom budget: `[propext, Classical.choice, Quot.sound]`; no `sorry`, no
`native_decide`.  There are no `axiom` declarations in the library.
-/
HDR
  # one `#print axioms` per name, grouped by declaring module (readable diffs)
  awk -F"$TAB" '
    function flush() {
      if (last != "") printf "\n-- %s (%d declarations)\n%s\n", last, n, buf
      buf = ""; n = 0
    }
    { if ($3 != last) { flush(); last = $3 }
      buf = buf "\n#print axioms " $1; n++ }
    END { flush() }' "$OUT/tools/audit-list.by-module.tsv"
} > "$OUT/$AUDIT_FILE"

# ----------------------------------------------------- 4. the coverage guard
if [ "$pariah_count" -eq 0 ]; then
  say "coverage guard: every library module is in the root's import closure"
elif [ "${AUDIT_SKIP_PARIAH:-0}" = 1 ]; then
  say "coverage guard SKIPPED (AUDIT_SKIP_PARIAH=1) -- $pariah_count module(s) unprobed"
else
  compile_mirror "$WORK/pariah" $(cat "$pariahs.only")
  probe=$WORK/PariahProbe.lean
  { for m in $(cat "$pariahs.only"); do echo "import $m"; done
    awk 'BEGIN{skip=1} skip && /^import /{next} {skip=0; print}' "$PKG/tools/AuditList.lean"
  } > "$probe"
  LEAN_PATH="$WORK/pariah:$AUDIT_OLEANS${LEAN_PATH:+:$LEAN_PATH}" \
    "$LEAN" "$probe" > "$OUT/tools/audit-pariah.tsv"
  cut -f1 "$OUT/tools/audit-pariah.tsv" | LC_ALL=C sort > "$WORK/pariah.names"
  cut -f1 "$OUT/tools/audit-list.by-module.tsv" | LC_ALL=C sort > "$WORK/main.names"
  if ! cmp -s "$WORK/pariah.names" "$WORK/main.names"; then
    echo "gen-audit: COVERAGE HOLE -- modules outside the root's import closure declare constants:" >&2
    LC_ALL=C comm -13 "$WORK/main.names" "$WORK/pariah.names" | sed 's/^/gen-audit:   unaudited: /' >&2
    echo "gen-audit: fix: import the module from FusionCategory/FusionCategory.lean (or delete it)" >&2
    exit 3
  fi
  say "coverage guard OK -- probing the $pariah_count pariah module(s) yields no name the main pass lacks"
fi

# --------------------------------------------------------------- 5. summary
say "$(wc -l < "$OUT/tools/audit-manifest.txt" | tr -d ' ') constants -> $OUT/tools/audit-manifest.txt"
cut -f2 "$OUT/tools/audit-list.tsv" | LC_ALL=C sort | uniq -c |
  sed 's/^ *\([0-9]*\) \(.*\)$/gen-audit:   \2: \1/'
say "   of the theorem-kind ones, $(awk -F"$TAB" '$4 == "1"' "$OUT/tools/audit-list.tsv" | wc -l | tr -d ' ') are structure projections (Lean's isProjectionFn)"
say "audit file -> $OUT/$AUDIT_FILE ($(wc -l < "$OUT/$AUDIT_FILE" | tr -d ' ') lines)"
