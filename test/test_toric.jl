module TestToric
using Test, Oscar, EquivariantBurnside

# True when f() throws an ArgumentError whose message contains the phrase.
function throws(phrase, f)
    try
        f()
    catch e
        return e isa ArgumentError && occursin(phrase, e.msg)
    end
    return false
end

const I2 = [1 0; 0 1]
const NUC = [0 -1; 1 -1]                    # order 3, the cyclic permutation of the coordinates (x:y:z) -> (z:x:y)
maps71(s, t, n; sign = 1) = [AffineTorusMap(I2, [sign * s // n, 0]), AffineTorusMap(I2, [0, sign * t // n]), AffineTorusMap(NUC, [0, 0])]
maps72(r, s, t; n = 14, m = 2) = [AffineTorusMap(I2, [r // m, 0]), AffineTorusMap(I2, [s // n, t // n]), AffineTorusMap(NUC, [0, 0])]
# isomorphism of the groups of two actions matching generators, as a GAP mapping (`fail` when it does not exist)
genhom(a1, a2) = GAP.Globals.GroupHomomorphismByImages(GAP.GapObj(a1.G), GAP.GapObj(a2.G),
                     GAP.GapObj([GAP.GapObj(g) for g in a1.gens]), GAP.GapObj([GAP.GapObj(g) for g in a2.gens]))
img(x) = x
zero_or_order(x) = is_zero(x) ? 1 : order(x)
const FAN12 = [[1,0],[2,1],[1,1],[1,2],[0,1],[-1,1],[-1,0],[-2,-1],[-1,-1],[-1,-2],[0,-1],[1,-1]]

@testset "2.1 affine maps, the group and the checks of ToricAction" begin
    f = AffineTorusMap(NUC, [1//8, 3//8])
    g = AffineTorusMap(I2, [7//8, 6//8])
    @test throws("determinant", () -> AffineTorusMap([1 1; 1 1], [0, 0]))
    @test throws("2 by 2", () -> AffineTorusMap([1 0 0; 0 1 0; 0 0 1], [0, 0, 0]))
    @test AffineTorusMap(I2, [9//8, -1//8]).t == [1//8, 7//8]               # reduced modulo 1
    act = ToricAction(maps71(1, 7, 8), toric_fan_P2())
    @test order(act.G) == 192 && length(act.images) == 192
    @test length(act.gens) == 3
    # the images of the generators are the given maps and the map is a homomorphism for the left convention
    for (g1, m) in zip(act.gens, maps71(1, 7, 8))
        @test act.images[g1] == m
    end
    for x in collect(act.G)[1:20], y in collect(act.G)[1:20]
        @test act.images[x * y].nu == act.images[x].nu * act.images[y].nu
    end
    # a group acting on the right: the same data is not a homomorphism for :left but is for :right
    S3 = symmetric_group(3)
    s1, s2 = cperm(S3, [1, 2]), cperm(S3, [2, 3])
    refl = AffineTorusMap([0 1; 1 0], [0, 0])
    rot = AffineTorusMap(NUC, [0, 0])
    gs = gens(S3)
    # an anti-homomorphism: send s1 to the swap and s2 to the rotation of order 3 composed so that (s1 s2)^3 fails
    @test throws("homomorphism", () -> ToricAction(S3, [AffineTorusMap(I2, [1//2, 0]), AffineTorusMap(I2, [0, 1//2])], toric_fan_P2()))
    # faithfulness: two elements with the same affine map
    G = symmetric_group(2)
    @test throws("not faithful", () -> ToricAction(G, [AffineTorusMap(I2, [0, 0])], toric_fan_P2()))
    # invalid fans
    @test throws("smooth cone", () -> ToricAction(maps71(1, 7, 8), [[1, 0], [1, 2], [-1, -1]]))
    @test throws("primitive", () -> ToricAction(maps71(1, 7, 8), [[2, 0], [0, 1], [-2, -1]]))
    @test throws("at least three", () -> ToricAction(maps71(1, 7, 8), [[1, 0], [-1, 0]]))
    # a fan that is not invariant under the linear part
    @test throws("not invariant", () -> ToricAction(maps71(1, 7, 8), [[1, 0], [1, 1], [0, 1], [-1, 0], [0, -1]]))
end

@testset "2.2 equivariant refinement" begin
    a = ToricAction(maps71(1, 7, 8), toric_fan_P2())
    @test equivariant_refinement(a) == toric_fan_hexagon()
    h = ToricAction(maps71(1, 7, 8), toric_fan_hexagon())
    @test equivariant_refinement(h) == toric_fan_hexagon()
    @test equivariant_refinement(ToricAction(maps71(1, 7, 8), FAN12)) == FAN12
    # only translations: no two rays of an orbit are adjacent, nothing to subdivide
    t = ToricAction([AffineTorusMap(I2, [1//3, 0])], toric_fan_P2())
    @test equivariant_refinement(t) == toric_fan_P2()
    # refine = false refuses a fan that violates the orbit condition
    @test throws("use refine = true", () -> toric_class(a; refine = false))
end

@testset "2.3 and 2.4 the class of the boundary strata" begin
    act = ToricAction(maps71(1, 7, 8), toric_fan_P2())
    cls = toric_class(act)
    @test length(cls.terms) == 4                          # two orbits of divisors and two orbits of vertices
    # the divisors have H of order 8 inside the group of translations and Y~ equal to the group of translations
    divs = [s for (_, s) in cls.terms if length(s.hg) == 1]
    verts = [s for (_, s) in cls.terms if length(s.hg) == 2]
    @test length(divs) == 2 && length(verts) == 2
    @test all(s -> s.ords == [8], divs) && all(s -> s.ords == [8, 8], verts)
    @test all(s -> length(s.betas) == 1, divs) && all(s -> length(s.betas) == 2, verts)
    # no symbols when there are no translations: the class is zero in BC_2
    c3 = ToricAction([AffineTorusMap(NUC, [0, 0])], toric_fan_P2())
    @test isempty(toric_class(c3).terms)
    # a translation along a ray gives a divisor symbol only
    t1 = ToricAction([AffineTorusMap(I2, [1//5, 0])], toric_fan_P2())
    @test length(toric_class(t1).terms) >= 1
    # reflections are refused
    refl = ToricAction([AffineTorusMap([0 1; 1 0], [0, 0])], toric_fan_P2())
    @test throws("reflections", () -> toric_class(refl))
end

@testset "2.3 and 2.4 weights against a hand computation on P^2" begin
    # C_5 acting by (x:y:z) -> (zeta x : y : z). In the coordinates (X, Y) = (x/z, y/z) the generator multiplies X by zeta.
    # The line {x = 0} is fixed pointwise with normal weight 1. The point [0:0:1] has weights (1, 0) and [0:1:0]
    # has weights (1, 0), both with a trivial character so they give no symbol. The point [1:0:0] has coordinates
    # (y/x, z/x) which are multiplied by (zeta^-1, zeta^-1), weights (4, 4). Hence the class is
    # (C_5, C_5, (1)) + (C_5, C_5, (4, 4)).
    act = ToricAction([AffineTorusMap(I2, [1//5, 0])], toric_fan_P2())
    a = act.gens[1]
    hand = BCClass(act.G, 2)
    push!(hand, BCSymbol(act.G, [a], [], [[1]]))
    push!(hand, BCSymbol(act.G, [a], [], [[4], [4]]))
    @test bc_image(toric_class(act)) == bc_image(hand)
    # the sign matters: weight 4 on the divisor gives a different class
    wrong = BCClass(act.G, 2)
    push!(wrong, BCSymbol(act.G, [a], [], [[4]]))
    push!(wrong, BCSymbol(act.G, [a], [], [[4], [4]]))
    @test bc_image(toric_class(act)) != bc_image(wrong)
    # C_5 acting by diag(1, zeta, zeta^2): the three fixed points have weights (1,2), (4,1) and (3,4)
    act2 = ToricAction([AffineTorusMap(I2, [1//5, 2//5])], toric_fan_P2())
    b = act2.gens[1]
    hand2 = BCClass(act2.G, 2)
    push!(hand2, BCSymbol(act2.G, [b], [], [[1], [2]]))
    push!(hand2, BCSymbol(act2.G, [b], [], [[4], [1]]))
    push!(hand2, BCSymbol(act2.G, [b], [], [[3], [4]]))
    @test bc_image(toric_class(act2)) == bc_image(hand2)
    @test length(toric_class(act2).terms) == 3          # three fixed points, the symbol (4, 1) is produced and vanishes by (V)
    @test is_zero(bc_image(BCSymbol(act2.G, [b], [], [[4], [1]]), 2))
end

# EBGLA Example 7.5, type (7.1) with n = 8, as a group of order 192
@testset "2.5 Example 7.5 from the fan of P^2" begin
    a1 = ToricAction(maps71(1, 7, 8), toric_fan_P2())
    a2 = ToricAction(maps71(3, 5, 8), toric_fan_P2())
    phi = genhom(a1, a2)
    @test phi !== GAP.Globals.fail && GAP.Globals.IsBijective(phi)
    c1, c2 = toric_class(a1), toric_class(a2)
    x1, x2 = bc_image(c1), bc_image(c2)
    @test !is_zero(x1) && !is_zero(x2) && order(x1) == 48 && order(x2) == 48
    d = bc_image(bc_transport(c1, phi) - c2)
    @test !is_zero(d) && order(d) == 3
    cert = certificate_nonzero(d)
    @test verify(cert) && verify_with_group(cert)
    # model independence: the hexagon given directly and a 12 ray fan give the same class
    h1 = ToricAction(maps71(1, 7, 8), toric_fan_hexagon())
    ph = genhom(h1, a1)
    @test bc_image(bc_transport(toric_class(h1), ph)) == x1
    t12 = ToricAction(maps71(1, 7, 8), FAN12)
    p12 = genhom(t12, a1)
    @test bc_image(bc_transport(toric_class(t12; refine = false), p12)) == x1
    # the Cremona involution conjugates the action to the one with t -> -t, which is equivariantly birational
    cr = ToricAction(maps71(1, 7, 8; sign = -1), toric_fan_P2())
    pc = genhom(cr, a1)
    @test bc_image(bc_transport(toric_class(cr), pc)) == x1
end

# The same class derived independently (by the project by hand and by Codex from the definition of the group)
GAP.evalstr("""
pt75 := function(i,j) return 8*(i mod 8)+(j mod 8)+1; end;;
Ta75 := PermList(List([0..63], k -> pt75(QuoInt(k,8)+1, k mod 8)));;
Tb75 := PermList(List([0..63], k -> pt75(QuoInt(k,8), (k mod 8)+1)));;
M175 := PermList(List([0..63], k -> pt75(k mod 8, -QuoInt(k,8)-(k mod 8))));;
M275 := M175^-1;;
G75d := fail;;
if M175*Ta75*M175^-1 = Tb75^-1 and M175*Tb75*M175^-1 = Ta75*Tb75^-1 then G75d := Group(Ta75,Tb75,M175);
elif M275*Ta75*M275^-1 = Tb75^-1 and M275*Tb75*M275^-1 = Ta75*Tb75^-1 then G75d := Group(Ta75,Tb75,M275); fi;;
""")

@testset "2.5 agreement with the two independent derivations of the class" begin
    G = GAP.Globals.G75d
    gg = GAP.Globals.GeneratorsOfGroup(G)
    a, b, c = gg[1], gg[2], gg[3]
    r = 7
    function codex_class(s, t; refined = false)
        out = BCClass(G, 2)
        add(h, y, w) = push!(out, BCSymbol(G, h, y, w))
        add([a], [b], [[s]]); add([a * b^r], [a, b], [[s]])
        for (w, v) in [([s, 0], [-s, t]), ([s, -t], [0, t])]
            if refined
                add([a, b], [], [w, v - w]); add([a, b], [], [w - v, v])
            else
                add([a, b], [], [w, v])
            end
        end
        if refined
            add([a * b^(2 * r)], [a, b], [[s]]); add([a^2 * b^r], [a, b], [[s]])
        end
        for _ in 1:3
            add([c], [], [[1]]); add([c], [], [[2]])
        end
        return out
    end
    for (s, t) in [(1, 7), (3, 5)]
        act = ToricAction(maps71(s, t, 8), toric_fan_P2())
        phi = GAP.Globals.GroupHomomorphismByImages(GAP.GapObj(act.G), G, GAP.GapObj([GAP.GapObj(g) for g in act.gens]), GAP.GapObj([a, b, c]))
        @test phi !== GAP.Globals.fail
        mine = bc_image(bc_transport(toric_class(act), phi))
        @test mine == bc_image(codex_class(s, t))
        @test mine == bc_image(codex_class(s, t; refined = true))
    end
end

@testset "2.5 Example 7.6, type (2) with n = 14 and m = 2" begin
    a1 = ToricAction(maps72(1, 3, 1), toric_fan_P2())
    a2 = ToricAction(maps72(1, 5, 1), toric_fan_P2())
    @test order(a1.G) == 84 && order(a2.G) == 84                       # 3 n m
    @test is_isomorphic(a1.G, a2.G)
    # matching generators does not give a homomorphism: the identification of the two groups is not obvious
    @test genhom(a1, a2) === GAP.Globals.fail
    iso = isomorphism(a1.G, a2.G)
    c1, c2 = toric_class(a1), toric_class(a2)
    reps = bc_out_automorphisms(a2.G)
    @test length(reps) == 6
    ords = sort([zero_or_order(bc_image(bc_transport(bc_transport(c1, iso), psi) - c2)) for psi in reps])
    # BC_2(G) separates the two actions for four classes of identifications and does not for two of them
    @test ords == [1, 1, 3, 3, 3, 3]
    @test bc_find_automorphism(c1, c2, iso) !== nothing
    @test throws("vanishes", () -> bc_inequivalence_certificates(c1, c2, iso))
end

end
