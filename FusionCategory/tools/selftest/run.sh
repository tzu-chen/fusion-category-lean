#!/bin/sh
# Gate 4 self-test: the gate must FAIL on every fixture in bad/ and PASS on
# every fixture in good/.  Any other outcome is a defect in the gate; a gate
# that has never been observed to fail is a report.
set -e
cd "$(dirname "$0")/../.."
stub="$PWD/tools/selftest/stub-bin"
rm -rf "$stub"; mkdir -p "$stub"
cat > "$stub/lake" <<'EOF'
#!/bin/sh
# self-test stub: replays a fixture instead of building/auditing
if [ "$1" = "build" ]; then exit 0; fi
cat "$GATE4_FIXTURE"
EOF
chmod +x "$stub/lake"
PATH="$stub:$PATH"
export GATE4_FIXTURE
fail=0
for f in tools/selftest/good/*.txt; do
  m="${f%.txt}.manifest"
  if [ -f "$m" ]; then export GATE4_MANIFEST="$PWD/$m"; else unset GATE4_MANIFEST || true; fi
  GATE4_FIXTURE="$PWD/$f"
  if sh tools/audit-gate.sh > /dev/null 2>&1; then
    echo "selftest: ok (gate passes)   : $f"
  else
    echo "selftest: DEFECT (gate should pass but fails): $f"; fail=1
  fi
done
for f in tools/selftest/bad/*.txt; do
  unset GATE4_MANIFEST || true
  GATE4_FIXTURE="$PWD/$f"
  if sh tools/audit-gate.sh > /dev/null 2>&1; then
    echo "selftest: DEFECT (gate should fail but passes): $f"; fail=1
  else
    echo "selftest: ok (gate fails)   : $f"
  fi
done
rm -rf "$stub"
[ "$fail" -eq 0 ] || exit 1
echo "selftest: every fixture behaved as required"
