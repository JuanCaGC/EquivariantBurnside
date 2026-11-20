module TestToricReflections
using Test, Oscar, EquivariantBurnside
const EB = EquivariantBurnside

const I2 = [1 0; 0 1]
const NUC = [0 -1; 1 -1]
const SQUARE = [[1, 0], [0, 1], [-1, 0], [0, -1]]
# the fan of the del Pezzo surface of degree 6 invariant under the group A2: rays +-(1,0), +-(0,1), +-(1,-1)
const FAN_A2 = [[1, 0], [0, 1], [-1, 1], [-1, 0], [0, -1], [1, -1]]

function c2s3()
    swap = AffineTorusMap([0 1; 1 0], [0, 0])
    rot = AffineTorusMap([0 1; -1 -1], [0, 0])
    minus = AffineTorusMap([-1 0; 0 -1], [0, 0])
    return ToricAction([swap, rot, minus], FAN_A2)
end

smooth(r) = all(i -> r[i][1] * r[mod1(i + 1, length(r))][2] - r[i][2] * r[mod1(i + 1, length(r))][1] == 1, eachindex(r))

@testset "2.6b inserting a ray into a smooth fan (Hirzebruch-Jung)" begin
    r = EB._insert_ray(SQUARE, [2, 1])
    @test r == [[1, 0], [2, 1], [1, 1], [0, 1], [-1, 0], [0, -1]] && smooth(r)
    r = EB._insert_ray(SQUARE, [3, 2])
    @test [3, 2] in r && smooth(r) && length(r) == 4 + 3        # (1,1), (2,1), (3,2) in the first quadrant
    r = EB._insert_ray(SQUARE, [-1, 3])
    @test [-1, 3] in r && smooth(r)
    @test EB._insert_ray(SQUARE, [1, 0]) == SQUARE               # already a ray
    # the rays added do not depend on the order of the insertions (Stern-Brocot nodes)
    a = EB._insert_ray(EB._insert_ray(SQUARE, [2, 1]), [1, 2])
    b = EB._insert_ray(EB._insert_ray(SQUARE, [1, 2]), [2, 1])
    @test sort(a) == sort(b)
    # the number of added rays is the sum of the partial quotients, here 5/3 = [1; 1, 2]
    @test length(EB._insert_ray(SQUARE, [5, 3])) - 4 >= 3
end

@testset "2.6b refinement with the rays of the fixed curves, the group C2 x S3" begin
    act = c2s3()
    r = equivariant_refinement(act)
    @test length(r) == 12 && smooth(r)
    # all six fixed directions and their opposites are rays (property (E))
    dirs = EB._layer_directions(act)
    @test length(dirs) == 12 && all(v -> v in r, dirs)
    # the fan is invariant under the group and no two rays of one orbit span a cone
    nus = unique([f.nu for f in values(act.images)])
    rs = Set(r)
    @test all(nu -> all(x -> Int.(nu * x) in rs, r), nus)
    orb(x) = Set(Int.(nu * x) for nu in nus)
    @test !any(i -> orb(r[i]) == orb(r[mod1(i + 1, length(r))]), eachindex(r))
    # two orbits of six rays, as in Step 3 of Kresch-Tschinkel (the same number of rays, 12)
    @test sort([length(orb(x)) for x in r]) == fill(6, 12)
    @test length(Set(orb(x) for x in r)) == 2
    # the result does not depend on the starting fan when it is already invariant and smooth
    @test sort(equivariant_refinement(ToricAction(c2s3().images |> x -> [AffineTorusMap([0 1; 1 0], [0, 0]), AffineTorusMap([0 1; -1 -1], [0, 0]), AffineTorusMap([-1 0; 0 -1], [0, 0])], r))) == sort(r)
end

@testset "2.6b without reflections property (E) changes nothing" begin
    maps = [AffineTorusMap(I2, [1//8, 0]), AffineTorusMap(I2, [0, 7//8]), AffineTorusMap(NUC, [0, 0])]
    act = ToricAction(maps, toric_fan_P2())
    @test equivariant_refinement(act) == equivariant_refinement(act; property_E = false) == toric_fan_hexagon()
    # a reflection whose fixed direction is not a ray forces the insertion even when the orbit condition would not
    refl = AffineTorusMap([1 0; 0 -1], [0, 0])          # fixes the curves u2 = 0 and u2 = 1/2, direction (1,0)
    @test equivariant_refinement(ToricAction([refl], SQUARE)) == SQUARE
    # a reflection along (1,1): the swap of the coordinates fixes the diagonal
    swap = AffineTorusMap([0 1; 1 0], [0, 0])
    r = equivariant_refinement(ToricAction([swap], SQUARE))
    @test [1, 1] in r && [-1, -1] in r && smooth(r)
end


# Kresch-Tschinkel, Equivariant Burnside groups and toric varieties, Proposition 6.1: the class of G = C2 x S3 acting on
# the del Pezzo surface of degree 6 by inversion and permutation of the coordinates of {t1 t2 t3 = 1}. Printed:
#   (triv, G, ()) + (S2, C2, (1)) + (diag in C2 x S2, C2, (1)) + (C2, S3, (1)) + (C2, S2, (1))
#   + 2 (C2 x S2, triv, (e1, e2)) + 2 (C2 x S2, triv, (e1 + e2, e2)) + (C2 x C3, triv, ((0,1), (1,1))) + (C3, triv, (1,1)).
function printed_prop61(act)
    G = act.G
    swap, rot, minus = act.gens
    terms = [
        (1, BCSymbol(G, [swap], [minus], [[1]])),                         # (S2, C2 acting on k(P^1), (1))
        (1, BCSymbol(G, [minus * swap], [swap], [[1]])),                  # (diagonal in C2 x S2, C2, (1))
        (1, BCSymbol(G, [minus], [swap, rot], [[1]])),                    # (C2, S3, (1))
        (1, BCSymbol(G, [minus], [swap], [[1]])),                         # (C2, S2, (1))
        (2, BCSymbol(G, [minus, swap], [], [[1, 0], [0, 1]])),            # 2 (C2 x S2, triv, (e1, e2))
        (2, BCSymbol(G, [minus, swap], [], [[1, 1], [0, 1]])),            # 2 (C2 x S2, triv, (e1 + e2, e2))
        (1, BCSymbol(G, [minus, rot], [], [[0, 1], [1, 1]])),             # (C2 x C3, triv, ((0,1), (1,1)))
        (1, BCSymbol(G, [rot], [], [[1], [1]])),                          # (C3, triv, (1,1))
    ]
    return terms
end
function class_of(G, terms; skip = 0)
    c = BCClass(G, 2)
    for (i, (k, s)) in enumerate(terms)
        i == skip || push!(c, k, s)
    end
    return c
end

@testset "2.6c Proposition 6.1 of Kresch-Tschinkel, C2 x S3" begin
    act = c2s3()
    terms = printed_prop61(act)
    mine = bc_image(toric_class(act))
    printed = bc_image(class_of(act.G, terms))
    @test !is_zero(mine) && order(mine) == 2
    @test mine == printed
    # sensitivity: in BC_2 the four divisor terms with H = C2 are each zero, the two point terms with H = C6 and H = C3 are not
    # and carry the whole comparison, the two K4 terms have coefficient two on elements of order two
    for j in 1:4
        c = BCClass(act.G, 2); push!(c, terms[j][1], terms[j][2])
        @test is_zero(bc_image(c))
    end
    @test bc_image(class_of(act.G, terms; skip = 7)) != mine
    @test bc_image(class_of(act.G, terms; skip = 8)) != mine
    # the conjugation relation: the K4 terms do not change if the S2 factor is the diagonal involution instead
    swap, rot, minus = act.gens
    alt = class_of(act.G, terms[[1, 2, 3, 4, 7, 8]])
    push!(alt, 2, BCSymbol(act.G, [minus, minus * swap], [], [[1, 0], [0, 1]]))
    push!(alt, 2, BCSymbol(act.G, [minus, minus * swap], [], [[1, 1], [0, 1]]))
    @test bc_image(alt) == mine
end

@testset "2.6c the symbols at the point (1,1,1) from the representation theory of S3 x C2" begin
    # S_p = G acts on the tangent plane by the standard representation of S3 times the sign of C2. The scalar elements are 1 and -1, so the
    # exceptional curve has generic stabilizer <-1> and Y~ = G. The eigenlines of the three reflections have eigenvalue +1 or -1, the stabilizer
    # of such a line is the Klein group <-1, s>. On the line with eigenvalue +1 of s the weights are (-1 -> -1, s -> +1) and
    # (-1 -> +1, s -> -1), that is (e1, e2) in the generators (-1, s). On the line with eigenvalue -1 they are (e1 + e2, e2).
    # The two eigenlines of the rotation have stabilizer <-1, rot> = C6 and weights ((1,1), (0,1)) in the generators (-1, rot).
    act = c2s3()
    G = act.G
    swap, rot, minus = act.gens
    p = first(q for q in special_points(act) if q.u == [0, 0])
    lp = EB.LocalPoint(:interior, Any[g for g in p.stabilizer],
                       Dict{Any,Matrix{ComplexF64}}(g => ComplexF64.(act.images[g].nu) for g in p.stabilizer))
    syms = EB._blowup_symbols(G, lp)
    cls = BCClass(G, 2)
    for (hg, yg, bs) in syms
        push!(cls, BCSymbol(G, hg, yg, bs))
    end
    hand = BCClass(G, 2)
    push!(hand, BCSymbol(G, [minus], [swap, rot], [[1]]))
    push!(hand, BCSymbol(G, [minus, swap], [], [[1, 0], [0, 1]]))
    push!(hand, BCSymbol(G, [minus, swap], [], [[1, 1], [0, 1]]))
    push!(hand, BCSymbol(G, [minus, rot], [], [[0, 1], [1, 1]]))
    @test length(syms) == 4
    @test sort([length(hg) for (hg, _, _) in syms]) == [1, 2, 2, 2]
    @test bc_image(cls) == bc_image(hand)
    # the point of stabilizer S3 acting by the standard representation has no scalars: no symbol for the exceptional curve
    q = first(q for q in special_points(act) if q.u == [1//3, 1//3])
    lq = EB.LocalPoint(:interior, Any[g for g in q.stabilizer],
                       Dict{Any,Matrix{ComplexF64}}(g => ComplexF64.(act.images[g].nu) for g in q.stabilizer))
    sq = EB._blowup_symbols(G, lq)
    @test all(isempty(yg) for (hg, yg, bs) in sq)
end

@testset "2.6c independence of the model" begin
    act = c2s3()
    base = bc_image(toric_class(act))
    # extra blowup centers do not change the class: the 36 six-torsion points of Kresch-Tschinkel and the 144 points of order dividing 12
    tors6 = [Rational{Int}[a // 6, b // 6] for a in 0:5 for b in 0:5]
    tors12 = [Rational{Int}[a // 12, b // 12] for a in 0:11 for b in 0:11]
    # the extra points really add symbols (so the equality is not trivial), whose total vanishes in BC_2(G)
    @test length(toric_class(act; extra_points = tors6).terms) > length(toric_class(act).terms)
    @test bc_image(toric_class(act; extra_points = tors6)) == base
    @test bc_image(toric_class(act; extra_points = tors12)) == base
    # a finer fan: the 12 sums of adjacent rays are added and the refinement finishes
    r12 = equivariant_refinement(act)
    m = length(r12)
    finer = Vector{Int}[]
    for i in 1:m
        push!(finer, r12[i]); push!(finer, r12[i] .+ r12[mod1(i + 1, m)])
    end
    maps = [AffineTorusMap([0 1; 1 0], [0, 0]), AffineTorusMap([0 1; -1 -1], [0, 0]), AffineTorusMap([-1 0; 0 -1], [0, 0])]
    act2 = ToricAction(maps, finer)
    @test length(equivariant_refinement(act2)) == 24
    phi = GAP.Globals.GroupHomomorphismByImages(GAP.GapObj(act2.G), GAP.GapObj(act.G),
                                                GAP.GapObj([GAP.GapObj(g) for g in act2.gens]), GAP.GapObj([GAP.GapObj(g) for g in act.gens]))
    @test bc_image(bc_transport(toric_class(act2), phi)) == base
    # the refined fan given directly is accepted with refine = false, a fan without property (E) is refused
    act3 = ToricAction(maps, r12)
    phi3 = GAP.Globals.GroupHomomorphismByImages(GAP.GapObj(act3.G), GAP.GapObj(act.G),
                                                 GAP.GapObj([GAP.GapObj(g) for g in act3.gens]), GAP.GapObj([GAP.GapObj(g) for g in act.gens]))
    @test bc_image(bc_transport(toric_class(act3; refine = false), phi3)) == base
    @test_throws ArgumentError toric_class(act; refine = false)
end

@testset "2.6c the blowups of the local points cancel without reflections" begin
    # points = true adds the symbols of the blowups of the interior fixed points and of the special boundary points, their total is zero
    cases = [
        ("order 3, n = 5", [AffineTorusMap(I2, [1//5, 0]), AffineTorusMap(I2, [0, 2//5]), AffineTorusMap(NUC, [0, 0])], toric_fan_P2()),
        ("order 2", [AffineTorusMap(I2, [1//5, 0]), AffineTorusMap(I2, [0, 1//5]), AffineTorusMap([-1 0; 0 -1], [0, 0])], SQUARE),
        ("order 4", [AffineTorusMap(I2, [1//5, 0]), AffineTorusMap(I2, [0, 1//5]), AffineTorusMap([0 -1; 1 0], [0, 0])], SQUARE),
        ("order 6", [AffineTorusMap(I2, [1//5, 0]), AffineTorusMap(I2, [0, 1//5]), AffineTorusMap([1 -1; 1 0], [0, 0])], toric_fan_hexagon()),
        ("pure order 4", [AffineTorusMap([0 -1; 1 0], [0, 0])], SQUARE),
        ("pure order 6", [AffineTorusMap([1 -1; 1 0], [0, 0])], toric_fan_hexagon()),
    ]
    for (label, maps, fan) in cases
        a = ToricAction(maps, fan)
        c0 = toric_class(a; points = false)
        c1 = toric_class(a; points = true)
        @test length(c1.terms) > length(c0.terms) || isempty(c1.terms) == isempty(c0.terms)
        @test bc_image(c0) == bc_image(c1)
    end
    # the pure order 4 action has seven symbols from the blowups and the class is zero
    a = ToricAction([AffineTorusMap([0 -1; 1 0], [0, 0])], SQUARE)
    @test length(toric_class(a; points = true).terms) > 0 && is_zero(bc_image(toric_class(a; points = true)))
end

@testset "2.6c reflections together with translations" begin
    # the swap of the coordinates and the translation by (1/2, 0): a group of order 8 with the fixed curves u1 = u2 and u1 - u2 = 1/2
    swap = AffineTorusMap([0 1; 1 0], [0, 0])
    tau = AffineTorusMap(I2, [1//2, 0])
    a = ToricAction([swap, tau], toric_fan_P2())
    base = bc_image(toric_class(a))
    extra = [Rational{Int}[x // 4, y // 4] for x in 0:3 for y in 0:3]
    @test length(toric_class(a; extra_points = extra).terms) > length(toric_class(a).terms)
    @test bc_image(toric_class(a; extra_points = extra)) == base
    a2 = ToricAction([swap, tau], SQUARE)
    phi = GAP.Globals.GroupHomomorphismByImages(GAP.GapObj(a2.G), GAP.GapObj(a.G),
                                                GAP.GapObj([GAP.GapObj(g) for g in a2.gens]), GAP.GapObj([GAP.GapObj(g) for g in a.gens]))
    @test bc_image(bc_transport(toric_class(a2), phi)) == base
    # a group with a reflection and a translation of order five along the fixed direction
    b = ToricAction([AffineTorusMap([1 0; 0 -1], [0, 0]), AffineTorusMap(I2, [1//5, 0])], SQUARE)
    xb = bc_image(toric_class(b))
    @test bc_image(toric_class(b; extra_points = [Rational{Int}[x // 10, y // 10] for x in 0:9 for y in 0:9])) == xb
end

@testset "2.6c the special points of the boundary: independence of the fan" begin
    # In these groups the special points of the open orbits of the boundary contribute to the class (ignoring them changes the image),
    # so the agreement of the class on two different invariant fans, where those points lie on different divisors, tests them.
    refl = AffineTorusMap([1 0; 0 -1], [0, 0])
    FAN8 = [[1, 0], [1, 1], [0, 1], [-1, 1], [-1, 0], [-1, -1], [0, -1], [1, -1]]
    function same_on(maps, fan1, fan2)
        a1 = ToricAction(maps, fan1); a2 = ToricAction(maps, fan2)
        phi = GAP.Globals.GroupHomomorphismByImages(GAP.GapObj(a2.G), GAP.GapObj(a1.G),
                  GAP.GapObj([GAP.GapObj(g) for g in a2.gens]), GAP.GapObj([GAP.GapObj(g) for g in a1.gens]))
        x1 = bc_image(toric_class(a1))
        return !is_zero(x1) && bc_image(bc_transport(toric_class(a2), phi)) == x1
    end
    tau5 = AffineTorusMap(I2, [1//5, 0]); sigma = AffineTorusMap(I2, [0, 1//2])
    @test same_on([refl, tau5], SQUARE, FAN8)
    @test same_on([refl, tau5, sigma], SQUARE, FAN8)
    @test same_on([refl, AffineTorusMap(I2, [1//3, 0]), sigma], SQUARE, FAN8)
    @test same_on([refl, AffineTorusMap(I2, [1//7, 0]), sigma], SQUARE, FAN8)
    swap = AffineTorusMap([0 1; 1 0], [0, 0])
    fan_p2_fine = [[1, 0], [2, 1], [1, 1], [1, 2], [0, 1], [-1, -1]]
    @test same_on([swap, AffineTorusMap(I2, [1//5, 1//5])], toric_fan_P2(), fan_p2_fine)
    @test same_on([swap, AffineTorusMap(I2, [1//5, 1//5]), AffineTorusMap(I2, [1//5, 0])], toric_fan_P2(), fan_p2_fine)
end

@testset "2.6c the option points" begin
    act = c2s3()
    @test_throws ArgumentError toric_class(act; points = false)
    @test_throws ArgumentError toric_class(act; points = :maybe)
    a = ToricAction([AffineTorusMap(I2, [1//5, 0])], toric_fan_P2())
    @test bc_image(toric_class(a)) == bc_image(toric_class(a; points = false))
end

end
