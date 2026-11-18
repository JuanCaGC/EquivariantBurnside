module TestTom
using Test
using EquivariantBurnside, Oscar
using Printf
function histogram(st)
    counts = Dict{Tuple,Int}()
    for h in st.hclasses
        d = Tuple(sort(h.d))
        counts[d] = get(counts, d, 0) + 1
    end
    join(["$(collect(d)) => $(counts[d])" for d in sort(collect(keys(counts)))], "; ")
end
function exact_classes(old, new, n)
    G = gapobj(symmetric_group(n))
    groups(st) = [GAP.evalstr("Group([" * join(h.Hgens, ",") * "])") for h in st.hclasses]
    a, b = groups(old), groups(new)
    matches = [findall(j -> sort(old.hclasses[i].d) == sort(new.hclasses[j].d) &&
                         GAP.Globals.IsConjugate(G, a[i], b[j]), eachindex(b)) for i in eachindex(a)]
    @test all(length(m) == 1 for m in matches)
    @test sort(only.(matches)) == collect(eachindex(b))
    true
end
begin
    old, new = Dict(), Dict()
    println("STEP 1: S4-S8 H-class comparison")
    for n in 4:8
        old[n] = bc_structure(symmetric_group(n); name="S$n")
        new[n] = bc_structure_tom(n)
        a, b = histogram(old[n]), histogram(new[n])
        println("S$n old H=$(length(old[n].hclasses)) new H=$(length(new[n].hclasses))")
        println("  old d multiplicities: ", a)
        println("  new d multiplicities: ", b)
        @test a == b
        @test exact_classes(old[n], new[n], n)
        @printf("  exact conjugacy bijection: PASS; pairs old=%d new=%d; structure seconds old=%.6f new=%.6f\n", npairs(old[n]), npairs(new[n]), old[n].gap_seconds, new[n].gap_seconds)
        flush(stdout)
    end
    println("STEP 2: old AND TomLib structures through unchanged bc(st,2)")
    expected = ["(Z/2)^3", "(Z/2)^6 × Z/4", "(Z/2)^31 × (Z/4)^3 × Z/8",
                "(Z/2)^57 × (Z/4)^12 × (Z/8)^2 × Z/3",
                "(Z/2)^290 × (Z/4)^30 × (Z/8)^6 × Z/16 × (Z/3)^2 × Z"]
    for n in 4:8
        a, b = bc(old[n], 2), bc(new[n], 2)
        println("S$n expected: ", expected[n-3])
        println("  old: ", format_ab(a.total))
        println("  TomLib: ", format_ab(b.total))
        @test a.total == b.total == ab(expected[n-3])
        @printf("  PASS; bc seconds old=%.6f new=%.6f\n", a.seconds, b.seconds)
        flush(stdout)
    end
end
end
