
function sweep_x() {
    local -n kvps=$1
    ((kvps["RobEntry"]+=1))
    ((kvps["Register"]+=1))
}

function sweep_y() {
    local -n kvps=$1
    ((kvps["InstrRecord"]+=1))
    ((kvps["steps"]+=1))
}

declare -a commands=(
    "check NoWAWHazard_WAWVulnerable for exactly {RobEntry}, exactly {Register}, {InstrRecord}, {steps}, 4 Int"
    "check NoWAWHazard_Complete for exactly {RobEntry}, exactly {Register}, {InstrRecord}, {steps}, 4 Int"
    "check NoWARHazard_WARVulnerable for exactly {RobEntry}, exactly {Register}, {InstrRecord}, {steps}, 4 Int"
    "check NoWARHazard_Complete for exactly {RobEntry}, exactly {Register}, {InstrRecord}, {steps}, 4 Int"
)
declare -a sweeps=(sweep_x sweep_y)
declare -A starting_point=("RobEntry" 2 "Register" 2 "InstrRecord" 6 "steps" 6)

