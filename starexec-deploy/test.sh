set -x
DEPLOY_BASE_DIR="$(pwd)"
RINGEN_SAMPLES_DIR="$(dirname "$DEPLOY_BASE_DIR")"/samples
cd bin
TMP_FOLDER="$DEPLOY_BASE_DIR"/tmp
STAREXEC_WALLCLOCK_LIMIT=32 ./starexec_run_cvc_tta_verbose $RINGEN_SAMPLES_DIR/prop_20.smt2 $TMP_FOLDER
