
commands=(
    "check NoWAWHazard_WAWVulnerable for exactly {RobEntry}, exactly {Register}, {InstrRecord}, {steps}, 4 Int"
    "check NoWAWHazard_Complete for exactly {RobEntry}, exactly {Register}, {InstrRecord}, {steps}, 4 Int"
    "check NoWARHazard_WARVulnerable for exactly {RobEntry}, exactly {Register}, {InstrRecord}, {steps}, 4 Int"
    "check NoWARHazard_Complete for exactly {RobEntry}, exactly {Register}, {InstrRecord}, {steps}, 4 Int"
)

declare -A parameters=("RobEntry" 4 "Register" 4 "InstrRecord" 10 "steps" 10)
function sweep1() {
    local -n kvps=$1
    ((kvps["RobEntry"]+=2))
    ((kvps["Register"]+=2))
}

for key in "${!parameters[@]}"; do
    echo "$key ${parameters[key]}"
done

declare -a sweep_funcs

