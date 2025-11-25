#!/bin/lua

local lyaml = require("lyaml")
local yaml_fname = arg[1]
local model_fname = arg[2]

local YELLOW_BOLD="\27[33;1m"
local GREEN_BOLD="\27[32;1m"
local RED_BOLD="\27[31;1m"
local RESET="\27[0m"

local function basename(path)
    local last_slash = path:match'^.*()/'
    if last_slash then
        return string.sub(path, last_slash + 1)
    else
        return path
    end
end

local function load_yaml(path)
    local f = assert(io.open(path, "r"))
    local content = f:read "*a"
    f:close()
    return lyaml.load(content)
end

local function run_single_test(f, model, run_command, vals)
    -- Prepare the run command.
    local com = run_command
    for i = 1, 2 do
        com = string.gsub(com, "{" .. i .. "}", vals[i])
    end

    -- Prepare the command summary.
    local summary = com
    summary = string.gsub(summary, "{", "")
    summary = string.gsub(summary, "}", "")
    summary = string.gsub(summary, "check ", "")
    summary = string.gsub(summary, "run ", "")
    summary = string.gsub(summary, " for ", ": ")
    summary = string.gsub(summary, "exactly ", "")

    -- Run the command.
    local handle = assert(io.popen(string.format("./test_model.sh \"%s\" \"%s\"", model, com)))
    local output = handle:read("*a")
    handle:close()

    -- Parse the result.
    local index = string.find(output, " ")
    local result = string.sub(output, 1, index - 1)
    local time = string.sub(output, index + 1, string.len(output) - 1)

    -- Print information about run.
    io.write(basename(model) .. " - " .. summary .. " - ")
    if result == 'TIMEOUT' then
        io.write(YELLOW_BOLD .. 'TIMEOUT' .. RESET)
    elseif string.find(run_command, "check") then
        if result == "SAT" then
            io.write(RED_BOLD .. 'COUNTER_EXAMPLE' .. RESET)
        else
            io.write(GREEN_BOLD .. 'VALID' .. RESET)
        end
    else
        if result == "SAT" then
            io.write(GREEN_BOLD .. 'SAT' .. RESET)
        else
            io.write(RED_BOLD .. 'UNSAT' .. RESET)
        end
    end
    print(": " .. time .. "ms")

    -- Write information about the run to a file.
    if result ~= 'TIMEOUT' then
        f:write(vals[1] .. "," .. vals[2] .. "," .. result .. "," .. time .. "\n")
    end

    -- Return the result
    return result ~= 'TIMEOUT'
end

local function sweeping(f, model, run_command, i, sweeps, starting_point)
    local vals = {}
    for k, v in pairs(starting_point) do
        vals[k] = v
    end
    local count = 0

    if i == #vals then
        while run_single_test(f, model, run_command, vals) do
            vals[i] = vals[i] + sweeps[i]
            count = count + 1
        end
    else
        while sweeping(f, model, run_command, i + 1, sweeps, vals) do
            vals[i] = vals[i] + sweeps[i]
            count = count + 1
        end
    end

    return count > 0
end

local function run_sweep(model, run_command, sweeps, starting_point, names)
    -- Slice off the name of the test from the run_command.
    local test_name = run_command
    local idx = string.find(test_name, " ")
    test_name = string.sub(test_name, idx + 1)
    idx = string.find(test_name, " ")
    test_name = string.sub(test_name, 1, idx - 1)

    -- Prepare the output file.
    local name = string.gsub(basename(model), ".als", "")
    local fname = "./output/" .. name .. "_" .. test_name
    local f = assert(io.open(fname, "w"))
    for _, n in ipairs(names) do
        f:write('"' .. n .. '",')
    end
    f:write('"Result","Time"\n')

    -- Call recursive helper to do the sweep.
    sweeping(f, model, run_command, 1, sweeps, starting_point)
end

local table = load_yaml(yaml_fname)
for _, command in ipairs(table['commands']) do
    run_sweep(model_fname, command, table['sweeps'], table['starting_point'], table['names'])
end


