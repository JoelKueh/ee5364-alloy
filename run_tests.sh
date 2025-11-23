
DIR="./"
TEMP_DIR="/tmp/alloy_tests"
TEMP_MODEL="$TEMP_DIR/model.alm"
TEMP_OUTPUT="$TEMP_DIR/results"
TEMP_RECEIPT="$TEMP_OUTPUT/receipt.json"
OUTPUT_FILE=./output/results.csv

GREEN_BOLD="\e[32;1m"
RED_BOLD="\e[31;1m"
NORM="\e[0m"

TIMEOUT=300

# Function that runs a single test on a model.
function run_single_test() {
    model=$1
    run_command=$2
    output_file=$3
    local -n kvps=$3

    # Write the model name to the output file.
    echo -n "$model," >>$output_file

    # Prepare run command and print debug infromation.
    for key in "${!kvps[@]}"; do
        run_command="${run_command//\{${key}\}/${kvps[${key}]} ${key}}"
    done
    echo -en "$NORM$model: $run_command - "

    # Create the output directory.
    mkdir -p $TEMP_DIR
    
    # Edit the file to contain our run command.
    rm -rf $TEMP_OUTPUT
    cp $model $TEMP_MODEL
    sed -i '/\/\/\*<BEGIN_RUN_COMMANDS>\*\/\//q' $TEMP_MODEL
    echo "$run_command" >>$TEMP_MODEL

    # Run the alloy analyzer on the model.
    if result=$(timeout $TIMEOUT alloy exec -d 1 -o $TEMP_OUTPUT -s minisat -f $TEMP_MODEL 2>&1); then
        echo 'TIMEOUT'
        return
    fi

    # Check the output of the analyzer for 
    if result | grep -q 'SAT'; then
        restlt='SAT'
    else
        result='UNSAT'
    fi
    start=$(awk -F '"utctime":' '{print $2}' $TEMP_RECEIPT | awk -F '}' '{print $1}')
    end=$(awk -F '"timestamp":' '{print $2}' $TEMP_RECEIPT | awk -F ',' '{print $1}')
    time=$(($start - $end))

    # Should print SAT/UNSAT for run commands and COUNTER_EXAMPLE/VALID
    if [[ "$run_command" == *check* ]]; then
        if [[ "$result" == "SAT" ]]; then
            echo -e $time'ms' - $RED_BOLD'COUNTER_EXAMPLE'
            result="COUNTER_EXAMPLE"
        else
            echo -e $time'ms' - $GREEN_BOLD'VALID'
            result="VALID"
        fi
    else
        if [[ "$result" == "SAT" ]]; then
            echo -e $time'ms' - $GREEN_BOLD'SAT'
        else
            echo -e $time'ms' - $RED_BOLD'UNSAT'
        fi
    fi

    # Return the result of the test.
    echo "$model,$run_command,$result,$time" >>$OUTPUT_FILE
}

function sweep_values() {
}

declare -A parameters=("RobEntry" 4 "Register" 4 "InstrRecord" 10 "steps" 10)
run_single_test \
    ./tomasulo/manual/tomasulo.als \
    "check NoWAWHazard_WAWVulnerable for exactly {RobEntry}, exactly {Register}, {InstrRecord}, {steps}, 4 Int" \
    $OUTPUT_FILE \
    parameters
    
    #"check NoWAWHazard_WAWVulnerable for exactly 4 RobEntry, exactly 4 Register, 10 InstrRecord, 10 steps, 4 Int"
    #"run {} for exactly 4 RobEntry, exactly 4 Register, 10 InstrRecord, 10 steps, 4 Int" \
