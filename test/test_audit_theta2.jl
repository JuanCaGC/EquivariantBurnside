module TestAuditTheta2
using Test, Oscar, EquivariantBurnside
const EB = EquivariantBurnside

# Evaluate every relation row of the defining presentation of BC_n(G) with the engine `bc_image`.
# Returns Dict(kind => (rows sent to a nonzero element, rows of that kind)).
function engine_on_rows(G, n; correction = true)
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
                              [Int.(ctx.chars[b]) for b in β]), n; blowup_correction = correction)
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

@testset "bc_image against the defining presentation of BC_n(G)" begin
    cases = [(symmetric_group(3), 2), (symmetric_group(3), 3), (dihedral_group(PermGroup, 8), 2),
             (abelian_group(PermGroup, [3, 3]), 2), (cyclic_group(PermGroup, 6), 2), (cyclic_group(PermGroup, 9), 2),
             (abelian_group(PermGroup, [4, 2]), 2), (abelian_group(PermGroup, [3, 3]), 3)]
    # With the restriction correction every relation of the definition is killed, kind by kind. This also checks
    # the translation of the generators of the presentation into symbols (the (C) rows in S3 and D4).
    for (G, n) in cases
        res = engine_on_rows(G, n)
        @test all(kv -> kv[2][1] == 0, res)
    end
    # The raw engine value (blowup_correction = false) does not kill the rows with a Theta_2 term. Pinned numbers.
    raw(G, n) = engine_on_rows(G, n; correction = false)
    @test raw(abelian_group(PermGroup, [3, 3]), 2)[:B_distinct_theta2] == (24, 24)
    @test raw(cyclic_group(PermGroup, 9), 2)[:B_distinct_theta2] == (6, 6)
    @test raw(cyclic_group(PermGroup, 6), 2)[:B_distinct_theta2] == (2, 5)
    @test raw(abelian_group(PermGroup, [4, 2]), 2)[:B_distinct_theta2] == (4, 22)
    @test raw(dihedral_group(PermGroup, 8), 2)[:B_distinct_theta2] == (0, 7)
    # the other kinds are respected by the raw value as well
    for k in (:V, :B_equal, :B_distinct, :C)
        res = raw(dihedral_group(PermGroup, 8), 2)
        haskey(res, k) && @test res[k][1] == 0
    end
end

end
