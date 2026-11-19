module TestAuditTheta2
using Test, Oscar, EquivariantBurnside
const EB = EquivariantBurnside

# Evaluate every relation row of the defining presentation of BC_n(G) with the engine `bc_image`.
# Returns Dict(kind => (rows sent to a nonzero element, rows of that kind)).
function engine_on_rows(G, n)
    Gg = gapobj(G)
    P = EB._direct_presentation(G, n)
    els = GAP.Globals.AsSSortedList(Gg)
    keys = Vector{Any}(undef, length(P.col))
    for (k, c) in P.col
        keys[c] = k
    end
    cache = Dict{Any,Any}()
    function elem(key)
        get!(cache, key) do
            i, y, β = key
            s = P.subs[i]
            ctx = EB.CharCtx(s.d)
            bc_image(BCSymbol(Gg, [els[p] for p in s.gens], [els[p] for p in P.allsubs[y]],
                              [Int.(ctx.chars[b]) for b in β]), n)
        end
    end
    res = Dict{Symbol,Tuple{Int,Int}}()
    for (r, k) in zip(P.rows, P.kinds)
        acc = nothing
        for (c, coef) in r
            x = coef * elem(keys[c])
            acc = acc === nothing ? x : acc + x
        end
        bad = (acc === nothing || is_zero(acc)) ? 0 : 1
        a, b = get(res, k, (0, 0))
        res[k] = (a + bad, b + 1)
    end
    return res
end

@testset "engine against the defining presentation (Theta_2 audit)" begin
    cases = [(symmetric_group(3), 2), (symmetric_group(3), 3), (dihedral_group(PermGroup, 8), 2),
             (abelian_group(PermGroup, [3, 3]), 2), (cyclic_group(PermGroup, 9), 2)]
    results = [engine_on_rows(G, n) for (G, n) in cases]
    # Relations (V), (B) with b1 = b2, (B) without the Theta_2 term and (C) are respected by the engine.
    # This also shows that the translation of generators of the presentation into symbols is right.
    for res in results, k in (:V, :B_equal, :B_distinct, :C)
        haskey(res, k) && @test res[k][1] == 0
    end
    # Pinned behavior on the relations with a Theta_2 term (see the audit in handoff/SPEC_FASE2.md section 7):
    # the engine does not kill them in C3 x C3 and in C9, and it does kill them in D4 (no difference there).
    @test results[3][:B_distinct_theta2] == (0, 7)
    @test results[4][:B_distinct_theta2] == (24, 24)
    @test results[5][:B_distinct_theta2] == (6, 6)
    # The property that the engine should have, a homomorphism from the group defined by the paper. Known failure.
    @test_broken all(res -> all(kv -> kv[2][1] == 0, res), results)
end

end
