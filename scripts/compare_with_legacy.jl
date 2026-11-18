# compare_with_legacy.jl
#
# Acceptance test A2 of Phase 0. It runs the four entry points of the new package, normalizes the
# output, and compares it with the outputs stored under legacy/bc. Only mathematical content is
# compared. Timings, shell `time` lines, GAP and mongoc warnings and column alignment are removed
# on both sides.
#
# Usage, from the package root:
#   julia --project=. scripts/compare_with_legacy.jl                 # new package versus stored legacy output
#   julia --project=. scripts/compare_with_legacy.jl --legacy-selftest   # fresh legacy run versus stored legacy output
#
# The selftest checks the oracle itself (the normalization and the determinism of the legacy outputs).
# Exit code 0 means every job matched, exit code 1 means a difference or a failed job.
#
# This file is owned by the reviewer. The implementer must not edit it.

const ROOT = dirname(@__DIR__)
const LEGACY = joinpath(ROOT, "legacy", "bc")
const BOOTSTRAP = joinpath(ROOT, "bootstrap.jl")

# Each job: label, stored file (relative to legacy/bc), new entry point (relative to ROOT) with args,
# and the legacy command (cwd legacy/bc) with args, used only by --legacy-selftest.
const JOBS = [
    ("validate all", "validation_output.txt",
        ["scripts/validate.jl", "all"], ["validate.jl", "all"]),
    ("bcclass tests", joinpath("proj", "bcclass_tests_output.txt"),
        ["scripts/bcclass_tests.jl"], [joinpath("proj", "bcclass_tests.jl")]),
    ("ex75", joinpath("proj", "ex75_output.txt"),
        ["scripts/ex75.jl"], [joinpath("proj", "ex75.jl")]),
    ("dcp tests", joinpath("proj", "dcp_validation_output.txt"),
        ["scripts/dcp_tests.jl"], [joinpath("proj", "dcp_tests.jl")]),
]

# Substitutions applied to every line, in order. The first one maps the one legacy header that contained
# an em-dash to its new wording, so that the new package does not have to print that character.
const SUBS = [
    (" \u2014 " => ": "),
    (r"\d+(\.\d+)?\s*seconds" => "<t> seconds"),
    (r"(\w*seconds)=\d+(\.\d+)?" => s"\1=<t>"),
    (r"\d+\.\d+s\b" => "<t>s"),
    (r"\s+" => " "),
]

# Lines dropped before comparison.
dropline(l) = isempty(strip(l)) || occursin("mongoc", l) || occursin("WARNING", l) ||
              occursin(r"^\s*(real|user|sys)\s", l) || occursin(r"^\s*TIME\s", l)

function normalize(text::AbstractString)
    out = String[]
    for l in split(text, '\n')
        dropline(l) && continue
        s = String(l)
        for (pat, rep) in SUBS
            s = replace(s, pat => rep)
        end
        push!(out, strip(s))
    end
    return out
end

function julia_cmd(dir, args)
    base = `$(Base.julia_cmd()) --project=$(dir) --startup-file=no`
    if dir == ROOT && isfile(BOOTSTRAP)
        base = `$base -L $BOOTSTRAP`
    end
    return Cmd(`$base $args`; dir=dir)
end

function run_job(dir, args)
    cmd = julia_cmd(dir, args)
    out = IOBuffer()
    t = @elapsed proc = run(pipeline(ignorestatus(cmd); stdout=out, stderr=devnull))
    return String(take!(out)), proc.exitcode, t
end

function main()
    selftest = "--legacy-selftest" in ARGS
    allok = true
    for (label, stored, newargs, oldargs) in JOBS
        storedtext = read(joinpath(LEGACY, stored), String)
        if selftest
            text, code, t = run_job(LEGACY, oldargs)
        else
            text, code, t = run_job(ROOT, newargs)
        end
        a = normalize(storedtext)
        b = normalize(text)
        same = a == b
        okexit = code == 0
        println("[", same && okexit ? " OK " : "FAIL", "] ", label, ": ", length(a), " stored lines, ",
                length(b), " produced lines, exit code ", code, ", ", round(t; digits=1), " s")
        if !same
            allok = false
            nshown = 0
            for i in 1:max(length(a), length(b))
                x = i <= length(a) ? a[i] : "<missing>"
                y = i <= length(b) ? b[i] : "<missing>"
                if x != y
                    println("    line $i stored:   ", x)
                    println("    line $i produced: ", y)
                    nshown += 1
                    nshown >= 10 && break
                end
            end
        end
        okexit || (allok = false)
    end
    println(allok ? "A2 RESULT: all jobs match" : "A2 RESULT: DIFFERENCES FOUND")
    exit(allok ? 0 : 1)
end

main()
