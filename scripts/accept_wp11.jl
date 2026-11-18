# accept_wp11.jl
#
# Acceptance test of work package 1.1. It compares the OSCAR route `bc_structure` with the retained
# GAP route `bc_structure_gap` (the Phase 0 implementation, kept unchanged as the oracle).
#
# Usage, from the package root:
#   julia --project=. scripts/accept_wp11.jl             # new route versus retained GAP route
#   julia --project=. scripts/accept_wp11.jl --selftest  # GAP route versus itself, checks the script only
#
# Checks:
#   1. For each test group, for n in the listed values, `bc(new)` and `bc(old)` have the same total
#      (printed form) and the same multiset of summands, where a summand is compared through
#      (Hdesc, sorted d, Ydesc, Ysize, orbitsize, stabsize, autsize, printed value).
#   2. The structure level data agree as multisets: (Hdesc, sorted d, classsize, Csize, Nsize, pairs).
#   3. A raw GAP group is accepted and gives the same total as the OSCAR group.
#   4. Timing on fresh groups in this process after a warm-up: the median of 3 fresh S_8 runs of the new
#      route must be at most 2 times the median of the old route, and at most 10 s.
#
# Exit code 0 when everything passes, 1 otherwise.
#
# This file is owned by the reviewer. The implementer must not edit it.

using Oscar, EquivariantBurnside
using Statistics: median
const EB = EquivariantBurnside

const SELFTEST = "--selftest" in ARGS
const OLD = SELFTEST ? EB.bc_structure : EB.bc_structure_gap
const NEW = EB.bc_structure

const GROUPS = [
    ("S3", () -> symmetric_group(3), [2, 3]),
    ("S4", () -> symmetric_group(4), [2, 3]),
    ("S5", () -> symmetric_group(5), [2, 3]),
    ("S6", () -> symmetric_group(6), [2, 3]),
    ("S7", () -> symmetric_group(7), [2]),
    ("A5", () -> alternating_group(5), [2, 3]),
    ("A6", () -> alternating_group(6), [2, 3]),
    ("D10", () -> dihedral_group(PermGroup, 10), [2, 3]),
    ("D14", () -> dihedral_group(PermGroup, 14), [2, 3]),
    ("He3 = SmallGroup(27,3)", () -> small_group(27, 3), [2, 3]),
    ("C5^2:C3 = SmallGroup(75,2)", () -> small_group(75, 2), [2]),
    ("SmallGroup(48,3)", () -> small_group(48, 3), [2, 3]),
    ("GL(2,3)", () -> general_linear_group(2, 3), [2, 3]),
]

summand_key(s) = (s.Hdesc, sort(s.d), s.Ydesc, s.Ysize, s.orbitsize, s.stabsize, s.autsize, string(s.value))
hclass_key(h) = (h.Hdesc, sort(h.d), h.classsize, h.Csize, h.Nsize,
                 sort([(Int(p[:Ysize]), Int(p[:orbitsize]), Int(p[:stabsize])) for p in h.pairs]))

nfail = Ref(0)
function check(ok, msg)
    println(ok ? "[ OK ] " : "[FAIL] ", msg)
    ok || (nfail[] += 1)
    return ok
end

function compare_group(label, mk, ns)
    stold = OLD(mk(); name = label)   # fresh group object for each route
    stnew = NEW(mk(); name = label)
    ok = sort(map(hclass_key, stold.hclasses); by = string) == sort(map(hclass_key, stnew.hclasses); by = string)
    check(ok, "$label structure data agree ($(length(stold.hclasses)) H classes, $(EB.npairs(stold)) pairs old, $(EB.npairs(stnew)) pairs new)")
    for n in ns
        rold = EB.bc(stold, n)
        rnew = EB.bc(stnew, n)
        tot = string(rold) == string(rnew)
        sums = sort(map(summand_key, rold.summands); by = string) == sort(map(summand_key, rnew.summands); by = string)
        check(tot && sums, "$label n=$n  old: $(rold)  new: $(rnew)" * (tot ? "" : "  TOTAL DIFFERS") * (sums ? "" : "  SUMMANDS DIFFER"))
    end
end

function fresh_times(route, runs)
    ts = Float64[]
    for _ in 1:runs
        G = symmetric_group(8)
        push!(ts, @elapsed route(G))
    end
    return ts
end

function main()
    println("route old = ", SELFTEST ? "bc_structure (selftest)" : "bc_structure_gap", ", route new = bc_structure")
    # warm-up, so that compilation is not timed
    OLD(symmetric_group(4)); NEW(symmetric_group(4))
    for (label, mk, ns) in GROUPS
        try
            compare_group(label, mk, ns)
        catch err
            check(false, "$label raised " * first(split(sprint(showerror, err), '\n')))
        end
    end
    # raw GAP group
    raw = EB.bc(GAP.Globals.SymmetricGroup(4), 2)
    ref = EB.bc(symmetric_group(4), 2)
    check(string(raw) == string(ref), "raw GAP group S4 accepted: $(raw)")
    # timing
    told = fresh_times(OLD, 3)
    tnew = fresh_times(NEW, 3)
    mo, mn = median(told), median(tnew)
    println("S8 fresh timings (s) old: ", round.(told; digits = 2), " new: ", round.(tnew; digits = 2))
    check(mn <= 2 * mo && mn <= 10, "S8 median new $(round(mn; digits = 2)) s, old $(round(mo; digits = 2)) s, limit min(2x old, 10 s) -> $(round(min(2 * mo, 10); digits = 2)) s")
    println(nfail[] == 0 ? "WP1.1 RESULT: all checks pass" : "WP1.1 RESULT: $(nfail[]) CHECK(S) FAILED")
    exit(nfail[] == 0 ? 0 : 1)
end

main()
