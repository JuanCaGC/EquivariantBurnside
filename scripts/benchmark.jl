# Sequential fresh-process benchmarks. No package load occurs in this driver.
using Dates
using Printf

const ROOT = dirname(@__DIR__)
const GROUPS = vcat(["S_$k" for k in 3:9], ["D_$p" for p in (5,7,11,13,17,19,23)],
                    ["He_$p" for p in (3,5,7)], ["C_8^2:C_3"])
const HEADER = ["group", "n", "route", "status", "structure_s", "bc_s", "alloc_bytes",
                "maxrss_bytes", "value", "n_pairs", "order", "check", "repetitions",
                "timeout_s", "wall_s", "reason"]
# Exact source lines in legacy/bc/validate.jl, in dictionary order:
# S_3: 85,86. S_4: 90,91. S_5: 95,96. S_6: 98,99.
# S_7: 155,156. S_8: 158,159. He_3: 129,130. He_5: 133,134.
# S_4 through S_8 at n=2 are also in test/test_tom.jl:39-41.
const EXPECTED = Dict(
    ("S_3",2)=>"Z/2", ("S_3",3)=>"0", ("S_4",2)=>"(Z/2)^3", ("S_4",3)=>"0",
    ("S_5",2)=>"(Z/2)^6 × Z/4", ("S_5",3)=>"0",
    ("S_6",2)=>"(Z/2)^31 × (Z/4)^3 × Z/8", ("S_6",3)=>"(Z/2)^5 × Z/4",
    ("S_7",2)=>"(Z/2)^57 × (Z/4)^12 × (Z/8)^2 × Z/3", ("S_7",3)=>"(Z/2)^16 × Z/4",
    ("S_8",2)=>"(Z/2)^290 × (Z/4)^30 × (Z/8)^6 × Z/16 × (Z/3)^2 × Z",
    ("S_8",3)=>"(Z/2)^122 × (Z/4)^4 × Z/8 × Z",
    ("He_3",2)=>"Z^26", ("He_3",3)=>"Z^4", ("He_5",2)=>"Z^124",
    ("He_5",3)=>"(Z/2)^36 × Z^36")

function options(args)
    smoke, timeout, only, out = false, 600.0, nothing, nothing
    i = 1
    while i <= length(args)
        arg = args[i]
        if arg == "--smoke"
            smoke = true
        elseif arg in ("--timeout", "--only", "--out")
            i += 1
            i <= length(args) || error("missing value for $arg")
            arg == "--timeout" && (timeout = parse(Float64, args[i]))
            arg == "--only" && (only = args[i])
            arg == "--out" && (out = args[i])
        else
            error("unknown option $arg")
        end
        i += 1
    end
    isfinite(timeout) && timeout > 0 || error("timeout must be positive and finite")
    only === nothing || only in GROUPS || error("unknown group $only, choose $(join(GROUPS, ", "))")
    smoke && out !== nothing && error("--smoke always uses a temporary output directory")
    return smoke, timeout, only, out
end

# Remove local identities from diagnostics before they enter public output.
function safe_reason(s)
    s = replace(string(s), ROOT => "<project>", homedir() => "<home>")
    s = replace(s, Regex("/" * "Users" * raw"/[^/\s]+") => "<home>", '\n' => ' ', '\r' => ' ', '\t' => ' ',
                '\u2014' => '-', ';' => ',')
    return first(s, min(length(s), 1000))
end

function child(name, n, route, timeout, scratch, rep)
    tag = replace("$(name)_$(n)_$(route)_$(rep)", r"[^A-Za-z0-9_]" => "_")
    output, errors = joinpath(scratch, tag * ".out"), joinpath(scratch, tag * ".err")
    base = Base.julia_cmd()
    # Optional runtime scaffolding is supplied by the caller, never hardcoded.
    boot = get(ENV, "BENCHMARK_BOOTSTRAP", "")
    flags = isempty(boot) ? String[] : ["-L", boot]
    cmd = `$base --project=$ROOT --startup-file=no $flags $(joinpath(@__DIR__, "support", "benchmark_case.jl")) $name $n $route`
    started = time_ns()
    timedout = false
    proc = nothing
    try
        open(output, "w") do stdout_file
            open(errors, "w") do stderr_file
                proc = run(pipeline(ignorestatus(cmd), stdout=stdout_file, stderr=stderr_file), wait=false)
                while process_running(proc)
                    if (time_ns() - started) / 1e9 >= timeout
                        timedout = true
                        kill(proc, Base.SIGKILL)
                        break
                    end
                    sleep(0.02)
                end
                wait(proc)
            end
        end
    finally
        if proc !== nothing && process_running(proc)
            kill(proc, Base.SIGKILL)
            wait(proc)
        end
    end
    wall = (time_ns() - started) / 1e9
    blank = ["", "", "", "", "", "", "", "", "", "", "", ""]
    if timedout
        blank[1], blank[9] = "timeout", "wall clock limit $(timeout) s including startup and warm-up"
        return blank, wall
    end
    lines = readlines(output)
    if proc.exitcode != 0 || length(lines) != 1 || length(split(only_line(lines), '\t', keepempty=true)) != 12
        diagnostic = read(errors, String)
        blank[1] = occursin(r"OutOfMemory|out of memory|Cannot allocate memory", diagnostic) ? "oom" : "crash"
        blank[9] = safe_reason("exit $(proc.exitcode), signal $(proc.termsignal), " * diagnostic)
        return blank, wall
    end
    row = String.(split(only(lines), '\t', keepempty=true))
    row[9] = safe_reason(row[9])
    return row, wall
end
only_line(lines) = length(lines) == 1 ? only(lines) : ""
median3(v) = sort(v)[cld(length(v), 2)]
number(x) = @sprintf("%.9f", x)
csvcell(x) = "\"" * replace(string(x), "\"" => "\"\"") * "\""

function machine()
    cpu = isempty(Sys.cpu_info()) ? "unknown" : first(Sys.cpu_info()).model
    kernel = strip(read(`uname -sr`, String))
    os = Sys.isapple() ? "macOS " * strip(read(`sw_vers -productVersion`, String)) : string(Sys.KERNEL)
    return "$cpu, $(Sys.CPU_THREADS) logical cores, $(Sys.total_memory()) bytes RAM, $os, $kernel"
end

function write_outputs(out, rows, versions, timeout, smoke)
    mkpath(out)
    open(joinpath(out, "benchmarks.csv"), "w") do io
        println(io, join(HEADER, ','))
        for row in rows
            println(io, join(csvcell.(row), ','))
        end
    end
    open(joinpath(out, "benchmarks.md"), "w") do io
        println(io, "# Performance baseline\n\nDate: $(Dates.today()).\n\nMachine: $(machine()).")
        println(io, "\nJulia $(versions[1]), OSCAR $(versions[2]), GAP $(versions[3]).")
        println(io, "\nThese are baseline numbers of this package on this machine and nothing is claimed about other software.")
        println(io, "\nRun `julia --project=. scripts/benchmark.jl` from the package root. Options are `--timeout SECONDS` (default 600), `--only NAME` and `--out DIR` (default `docs/src` for the full run, a temporary directory for `--only`). Names match the group column, with `C_8^2:C_3` quoted in a shell. `--smoke` selects S_3, S_4, D_5 and He_3 at n = 2, uses oscar for S_3 and He_3, gap for D_5 and tom for S_4 with one repetition per group, prints its table and writes results into `mktempdir()` only. Smoke mode cannot overwrite the baseline.")
        println(io, "\nEach case runs in a fresh Julia child, sequentially. An S_4 warm-up uses the same n and dispatch route before a fresh group is constructed. TomLib has no S_3 table on this installation. For the S_4 tom target, the S_4 library table used in warm-up can remain cached inside GAP. This small-case caveat is part of this baseline. Group construction, loading, warm-up and the explicit Julia GC before measurement are excluded from structure_s and bc_s. The two steps use @timed. Structure includes the complete bc_structure or bc_structure_tom call. The bc step uses the resulting structure and a new default cache. Warm-up reduces compilation cost but cannot eliminate specialization first encountered in larger groups.")
        println(io, "\nEvery group has an oscar route calling bc_structure on an OSCAR PermGroup and a gap route calling bc_structure_gap. Heisenberg and C_8^2:C_3 constructors copy the existing GAP constructions and wrap them using Oscar._oscar_group before either route is measured. Symmetric groups also have a tom route calling bc_structure_tom(k). The full matrix has 86 rows.")
        println(io, "\nIf the first measured structure_s + bc_s is under 10 seconds, there are three fresh children, otherwise one. Smoke always uses one. Times and allocation bytes are componentwise medians, maxrss_bytes is the maximum over repetitions. wall_s is the sum of whole child wall times. Repetition values, orders and pair counts must agree. n_pairs counts classes [H,Y]. value is the package's printed BC_n(G) abelian group.")
        println(io, "\nalloc_bytes counts Julia allocations in the two measured steps, not GAP allocations. maxrss_bytes is Sys.maxrss() in bytes and measures the peak of the whole child process, including startup, compilation, warm-up and GAP memory. The wall timeout includes all of those stages and is enforced per child at $(timeout) seconds. A timeout is retained with its limit. If n = 2 times out for a group and route, n = 3 is skipped with reason `n=2 already exceeded the limit`. A skipped row is not a measurement and has blank metrics with zero repetitions. An OOM requires explicit diagnostic evidence, an unexplained signal is reported as a crash. Failed repetitions are retained and are never averaged into successful data.")
        println(io, "\nExact expected-value sources in legacy/bc/validate.jl are lines 85,86 (S_3), 90,91 (S_4), 95,96 (S_5), 98,99 (S_6), 155,156 (S_7), 158,159 (S_8), 129,130 (He_3) and 133,134 (He_5), in n = 2,3 order. test/test_tom.jl lines 39-41 independently list S_4 through S_8 at n = 2. checked means equality to that expected string. Other results are unchecked. A mismatch or inconsistent repetition makes the driver exit nonzero. CSV contains the same columns and full numeric precision as this table.")
        println(io, "\nRuntime flags are inherited through Base.julia_cmd(). In restricted environments BENCHMARK_BOOTSTRAP may name an optional Julia file to load in each child. Runtime scratch configuration is the caller's responsibility. For timing comparisons keep the machine otherwise idle. $(smoke ? "This is a smoke run." : "This is the full baseline run or a selected subset.")\n")
        println(io, "| ", join(HEADER, " | "), " |")
        println(io, "| ", join(fill("---", length(HEADER)), " | "), " |")
        for row in rows
            println(io, "| ", join(replace.(string.(row), "|" => "\\|"), " | "), " |")
        end
    end
end

routes(name, smoke) = smoke ? (name == "S_4" ? ("tom",) : name == "D_5" ? ("gap",) : ("oscar",)) :
    (startswith(name, "S_") ? ("oscar", "gap", "tom") : ("oscar", "gap"))

function run_benchmark(out, smoke, timeout, selected)
    groups = smoke ? ["S_3", "S_4", "D_5", "He_3"] : GROUPS
    selected === nothing || (groups = filter(==(selected), groups))
    isempty(groups) && error("selected group is outside the smoke set")
    rows = Vector{String}[]
    versions = ["unknown", "unknown", "unknown"]
    failed = false
    timed_out = Set{Tuple{String,String}}()
    mktempdir() do scratch
        for name in groups, n in (smoke ? (2,) : (2,3)), route in routes(name, smoke)
            if n == 3 && (name, route) in timed_out
                row = vcat([name, string(n), route, "skipped"], fill("", 7),
                           ["unchecked", "0", string(timeout), "", "n=2 already exceeded the limit"])
                push!(rows, row)
                write_outputs(out, rows, versions, timeout, smoke)
                println(join(row, " | "))
                flush(stdout)
                continue
            end
            firstrow, wall = child(name, n, route, timeout, scratch, 1)
            samples = [firstrow]
            if firstrow[1] == "ok" && !smoke && parse(Float64, firstrow[2]) + parse(Float64, firstrow[3]) < 10
                for rep in 2:3
                    sample, elapsed = child(name, n, route, timeout, scratch, rep)
                    push!(samples, sample)
                    wall += elapsed
                    sample[1] == "ok" || break
                end
            end
            for sample in samples
                sample[10] == "" || (versions = sample[10:12])
            end
            bad = findfirst(s -> s[1] != "ok", samples)
            data = copy(bad === nothing ? firstrow : samples[bad])
            check = "unchecked"
            if bad === nothing
                for col in 2:4
                    data[col] = col == 4 ? string(median3(parse.(Int, getindex.(samples, col)))) : number(median3(parse.(Float64, getindex.(samples, col))))
                end
                data[5] = string(maximum(parse.(Int, getindex.(samples, 5))))
                expected = get(EXPECTED, (name,n), nothing)
                if any(s -> s[6:8] != firstrow[6:8], samples)
                    data[1], data[9], check = "mismatch", "repetitions disagree", "mismatch"
                elseif expected !== nothing
                    check = data[6] == expected ? "checked" : "mismatch"
                    if check == "mismatch"
                        data[1], data[9] = "mismatch", "expected $expected"
                    end
                end
            else
                data[2:4] .= ""
                data[9] = "repetition $bad of $(length(samples)): " * data[9]
            end
            n == 2 && data[1] == "timeout" && push!(timed_out, (name, route))
            failed |= data[1] in ("mismatch", "error", "crash") || (smoke && data[1] != "ok")
            row = vcat([name, string(n), route, data[1]], data[2:8], [check, string(length(samples)), string(timeout), number(wall), data[9]])
            push!(rows, row)
            write_outputs(out, rows, versions, timeout, smoke)
            println(join(row, " | "))
            flush(stdout)
        end
    end
    return failed ? 1 : 0
end

function main()
    smoke, timeout, selected, out = options(ARGS)
    println(join(HEADER, " | "))
    if smoke
        # cleanup=true removes all result files when the driver exits.
        out = mktempdir()
        return run_benchmark(out, smoke, timeout, selected)
    end
    destination = out === nothing ? (selected === nothing ? joinpath(ROOT, "docs", "src") : mktempdir()) : out
    return run_benchmark(destination, smoke, timeout, selected)
end
abspath(PROGRAM_FILE) == (@__FILE__) && exit(main())
