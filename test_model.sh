
TEMP_DIR="/tmp/alloy_tests"
TEMP_MODEL="$TEMP_DIR/model.als"
TEMP_OUTPUT="$TEMP_DIR/results"
TEMP_RECEIPT="$TEMP_OUTPUT/receipt.json"
TIMEOUT="1000.0s"

model=$1
run_command=$2

# Edit the file to contain our run command.
mkdir -p $TEMP_DIR
rm -rf $TEMP_OUTPUT
cp $model $TEMP_MODEL
sed -i '/\/\/\*<BEGIN_RUN_COMMANDS>\*\/\//q' $TEMP_MODEL
echo "$run_command" >>$TEMP_MODEL

# Run the alloy analyzer on the model.
start_ms=$(date +%s%3N)
result=$(timeout $TIMEOUT alloy exec -d 1 -o $TEMP_OUTPUT -s minisat -f $TEMP_MODEL 2>&1);
exit_code=$?
end_ms=$(date +%s%3N)

# Exit early if we timed out.
if [[ $exit_code != 0 ]]; then
    echo 'TIMEOUT -1'
    exit
fi

# Echo the result.
if [[ $result == *SAT* ]]; then
    result='SAT'
else
    result='UNSAT'
fi
time=$(($end_ms - $start_ms))
echo "$result $time"
