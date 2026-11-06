#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

if [[ $# != 0 && !( $# == 1 && "$1" == --preflight ) ]]; then
  echo 'Usage: bash scripts/check.sh [--preflight]' >&2
  exit 2
fi

run_step() {
  local label=$1 started=$SECONDS status=0
  shift
  printf '\n[check] %s: starting\n' "$label"
  "$@" || status=$?
  printf '[check] %s: exit %s, %ss\n' "$label" "$status" "$((SECONDS - started))"
  return "$status"
}

# [impl->req~lean-validation~1]
# [itest->req~lean-validation~1]
export PYTHONDONTWRITEBYTECODE=1
validation_mode=full
if [[ -n "${CLAFER_VALIDATION_PLAN:-}" ]]; then
  validation_mode=$(python3 scripts/validation.py select --plan "$CLAFER_VALIDATION_PLAN")
fi
printf '[check] Validation mode: %s\n' "$validation_mode"
validation_dir=.lake/validation
# Catch source/inventory mistakes before installing Lean or preparing dependencies.
run_step 'Module inventory' python3 scripts/project_modules.py --output-dir "$validation_dir"
run_step 'Module regressions' python3 -m unittest discover -s tests -p test_project_modules.py -v

if [[ "${1:-}" == --preflight ]]; then
  exit 0
fi

run_step 'Documentation links' python3 scripts/check_docs.py
if [[ "$validation_mode" == docs ]]; then
  run_step 'Documentation regressions' python3 -m unittest discover -s tests -p test_check_docs.py -v
  run_step 'Validation selection regressions' python3 -m unittest discover -s tests -p test_validation.py -v
  printf '[check] Documentation validation complete; no new Lean validation claimed.\n'
  exit 0
fi

# Caching is opt-in and keyed by Lake's source/options/import traces. Restore
# every artifact locally so the audit and leanchecker inspect this build.
export LAKE_ARTIFACT_CACHE="${LAKE_ARTIFACT_CACHE:-false}"
export LAKE_RESTORE_ARTIFACTS=true

# IntentMade supplies this trusted profile to provision the pinned Lean toolchain.
if [[ -n "${FACTORY_TESTS:-}" && -f "$FACTORY_TESTS/lean-env.sh" ]]; then
  printf '\n[check] Lean toolchain: starting\n'
  started=$SECONDS
  source "$FACTORY_TESTS/lean-env.sh"
  printf '[check] Lean toolchain: exit 0, %ss\n' "$((SECONDS - started))"
fi

# Dependency provisioning is optional; the build and kernel checks always run.
mapfile -t mathlib_imports < "$validation_dir/mathlib-imports.txt"
# An empty argument list would download all of Mathlib, not an empty set.
if (( ${#mathlib_imports[@]} )); then
  if ! run_step 'Mathlib cache' lake exe cache get "${mathlib_imports[@]}"; then
    echo 'Mathlib cache unavailable; building the pinned dependencies from source.' >&2
  fi
fi
# Use the discovered inventory at every stage, including modules not reachable
# from an entrypoint (notably examples and future internal helpers).
mapfile -t modules < "$validation_dir/modules.txt"
run_step 'Library and module build' lake build DPGraph FormalCD Clafer "${modules[@]/#/+}"
# Run the audit and regression gates before the more expensive kernel replay.
# An invalid candidate should fail before rechecking all compiled project proofs.
run_step 'Axiom audit' lake env lean -DwarningAsError=true "$validation_dir/axiom_audit.lean"
while IFS= read -r source; do
  run_step "Lean test $source" lake env lean -DwarningAsError=true "$source"
done < "$validation_dir/tests.txt"

python_tests=(python3 -m unittest discover -s tests -v)
if [[ "${CLAFER_TEST_JOBS:-1}" != 1 ]]; then
  python_tests=(python3 scripts/run_tests.py --jobs "$CLAFER_TEST_JOBS")
fi
run_step 'Python tests (including Lean audit fixtures)' \
  python3 scripts/verification/runtime.py lake env "${python_tests[@]}"

# leanchecker recursively enumerates each public root, including unimported
# helpers/examples. Avoid rescanning every dependency directory for each leaf.
run_step 'Kernel checks (all discovered modules)' \
  env LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}" \
  lake env leanchecker --verbose DPGraph FormalCD Clafer
