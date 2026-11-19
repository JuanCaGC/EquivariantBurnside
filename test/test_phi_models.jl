module TestPhiModels
using Test, Oscar, EquivariantBurnside

# The monomial action (7.1) of EBGLA on P^2 with n = 8, in the group of order 192 of Example 7.5.
# Classes for two standard models of the same action, derived independently by two authors (the project and
# Codex): the model with 6 boundary rays, and the model with 12 rays obtained by blowing up its six vertices.
# The class of an action does not depend on the model, so both must have the same image in BC_2(G).
GAP.evalstr("""
pt75 := function(i,j) return 8*(i mod 8)+(j mod 8)+1; end;;
Ta75 := PermList(List([0..63], k -> pt75(QuoInt(k,8)+1, k mod 8)));;
Tb75 := PermList(List([0..63], k -> pt75(QuoInt(k,8), (k mod 8)+1)));;
M175 := PermList(List([0..63], k -> pt75(k mod 8, -QuoInt(k,8)-(k mod 8))));;
M275 := M175^-1;;
G75c := fail;;
if M175*Ta75*M175^-1 = Tb75^-1 and M175*Tb75*M175^-1 = Ta75*Tb75^-1 then G75c := Group(Ta75,Tb75,M175);
elif M275*Ta75*M275^-1 = Tb75^-1 and M275*Tb75*M275^-1 = Ta75*Tb75^-1 then G75c := Group(Ta75,Tb75,M275); fi;;
""")

function toric_class(G, a, b, c, n, r, s, t; refined = false)
    out = BCClass(G, 2)
    add(h, y, w) = push!(out, BCSymbol(G, h, y, w))
    add([a], [b], [[s]])
    add([a * b^r], [a, b], [[s]])
    for (w, v) in [([s, 0], [-s, t]), ([s, -t], [0, t])]
        if refined
            add([a, b], [], [w, v - w])
            add([a, b], [], [w - v, v])
        else
            add([a, b], [], [w, v])
        end
    end
    if refined
        add([a * b^(2 * r)], [a, b], [[s]])
        add([a^2 * b^r], [a, b], [[s]])
    end
    for _ in 1:3     # the point orbits with stabilizer C_3 (3 does not divide n)
        add([c], [], [[1]])
        add([c], [], [[2]])
    end
    return out
end

@testset "model independence and Example 7.5 with the restriction correction" begin
    G = GAP.Globals.G75c
    gg = GAP.Globals.GeneratorsOfGroup(G)
    a, b, c = gg[1], gg[2], gg[3]
    n, r = 8, 7
    @test c * a * c^-1 == b^r && c * b * c^-1 == a * b^-1   # alpha^(-1/r) beta^-1 with -1/7 = 1 mod 8
    for (s, t) in [(1, 7), (3, 5)]
        x6 = bc_image(toric_class(G, a, b, c, n, r, s, t))
        x12 = bc_image(toric_class(G, a, b, c, n, r, s, t; refined = true))
        @test x6 == x12
        # the raw engine value is not invariant under the blowup
        y6 = bc_image(toric_class(G, a, b, c, n, r, s, t); blowup_correction = false)
        y12 = bc_image(toric_class(G, a, b, c, n, r, s, t; refined = true); blowup_correction = false)
        @test y6 != y12
    end
    d = toric_class(G, a, b, c, n, r, 1, 7) - toric_class(G, a, b, c, n, r, 3, 5)
    x = bc_image(d)
    @test !is_zero(x) && order(x) == 3
    cert = certificate_nonzero(x)
    @test verify(cert) && verify_with_group(cert)
    # the same verdict on the refined models
    d2 = toric_class(G, a, b, c, n, r, 1, 7; refined = true) - toric_class(G, a, b, c, n, r, 3, 5; refined = true)
    @test bc_image(d2) == x
end

@testset "blowup relation with the Theta_2 term in C_3 x C_3" begin
    G = abelian_group(PermGroup, [3, 3])
    x, y = gens(G)
    s = BCSymbol(G, [x, y], [], [[1, 0], [0, 1]])
    t1 = BCSymbol(G, [x, y], [], [[1, 2], [0, 1]])
    t2 = BCSymbol(G, [x, y], [], [[1, 0], [2, 1]])
    th2 = BCSymbol_preimage(G, [x * y], [x, y], [[1]])
    c = BCClass(G, 2)
    push!(c, 1, s); push!(c, -1, t1); push!(c, -1, t2); push!(c, -1, th2)
    @test is_zero(bc_image(c))                                        # the relation (B) with Theta_2
    c0 = BCClass(G, 2)
    push!(c0, 1, s); push!(c0, -1, t1); push!(c0, -1, t2)
    @test !is_zero(bc_image(c0))                                      # Theta_2 itself is not zero
    @test is_zero(bc_image(c0; blowup_correction = false))            # the raw engine drops Theta_2
end

end
