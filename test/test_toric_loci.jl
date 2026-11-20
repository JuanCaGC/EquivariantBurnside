module TestToricLoci
using Test, Oscar, EquivariantBurnside

const I2 = [1 0; 0 1]
const NUC = [0 -1; 1 -1]
# the fan of the del Pezzo surface of degree 6 invariant under the group A2: rays +-(1,0), +-(0,1), +-(1,-1)
const FAN_A2 = [[1, 0], [0, 1], [-1, 1], [-1, 0], [0, -1], [1, -1]]

@testset "fixed sets of single maps (hand computations)" begin
    @test fixed_set(AffineTorusMap(I2, [0, 0])) == (:all,)
    @test fixed_set(AffineTorusMap(I2, [1//3, 0])) == (:points, Vector{Rational{Int}}[])
    # inversion -1: u = -u mod 1, the four points of order two
    kind, pts = fixed_set(AffineTorusMap([-1 0; 0 -1], [0, 0]))
    @test kind == :points && pts == sort([[0, 0], [0, 1//2], [1//2, 0], [1//2, 1//2]])
    # inversion composed with a translation by t: u = (-u + t) so 2u = t, four points u = t/2 + (a/2, b/2)
    kind, pts = fixed_set(AffineTorusMap([-1 0; 0 -1], [1//2, 0]))
    @test kind == :points && pts == sort([[1//4, 0], [1//4, 1//2], [3//4, 0], [3//4, 1//2]])
    # rotation of order three: three fixed points
    kind, pts = fixed_set(AffineTorusMap(NUC, [0, 0]))
    @test kind == :points && length(pts) == 3
    # the swap of the coordinates fixes the diagonal u1 = u2
    kind, ls = fixed_set(AffineTorusMap([0 1; 1 0], [0, 0]))
    @test kind == :layers && ls == [FixedLayer([1, -1], 0)]
    # a swap composed with a translation along the diagonal still fixes a curve, along the antidiagonal it fixes none
    @test fixed_set(AffineTorusMap([0 1; 1 0], [1//5, 1//5]))[1] == :layers
    @test isempty(fixed_set(AffineTorusMap([0 1; 1 0], [1//2, 0]))[2])
    # the reflection diag(1, -1) fixes two curves u2 = 0 and u2 = 1/2
    kind, ls = fixed_set(AffineTorusMap([1 0; 0 -1], [0, 0]))
    @test kind == :layers && Set(ls) == Set([FixedLayer([0, 1], 0), FixedLayer([0, 1], 1//2)])
    # every point of a reported layer is fixed
    for f in (AffineTorusMap([0 1; 1 0], [1//5, 1//5]), AffineTorusMap([1 0; 0 -1], [0, 1//3]), AffineTorusMap([0 -1; -1 0], [1//7, 1//7]))
        kind, ls = fixed_set(f)
        for l in ls
            u0 = l.m[1] != 0 ? Rational{Int}[l.c // l.m[1], 0] : Rational{Int}[0, l.c // l.m[2]]
            v = [-l.m[2], l.m[1]]
            for k in 0:3
                u = u0 .+ k .* v .// 3
                @test all(isinteger, EquivariantBurnside._apply(f, u) .- u)
            end
        end
    end
    @test_throws ArgumentError FixedLayer([2, 2], 0)
end

# Kresch-Tschinkel, Equivariant Burnside groups and toric varieties, Section 6: G = C2 x S3 acting on the torus
# {t1 t2 t3 = 1} by inversion and permutations of the coordinates. Printed: Step 1, the lattice L' of
# distinguished stabilizers (six subgroups of order two with one dimensional fixed subtori), Step 4, the stabilizer locus
# (1,1,1), (-1,-1,1), (-1,1,-1), (1,-1,-1), (zeta,zeta,zeta), (zeta^2,zeta^2,zeta^2), and Table 1, the stabilizers
# of these points, G for (1,1,1), K4 for the three points of order two and S3 for the two points with zeta.
@testset "Kresch-Tschinkel Section 6: the group C2 x S3" begin
    swap = AffineTorusMap([0 1; 1 0], [0, 0])
    rot = AffineTorusMap([0 1; -1 -1], [0, 0])
    minus = AffineTorusMap([-1 0; 0 -1], [0, 0])
    act = ToricAction([swap, rot, minus], FAN_A2)
    @test order(act.G) == 12
    fc = fixed_curves(act)
    @test length(fc) == 6
    @test all(c -> length(c.H) == 2, fc)                    # the generic stabilizer of each curve is a subgroup of order two
    sp = special_points(act)
    @test length(sp) == 6
    # coordinates (u1, u2) = (log t1, log t2) / 2 pi i, t3 = (t1 t2)^-1: the printed points of the stabilizer locus
    expected = Dict([0, 0] => 12, [0, 1//2] => 4, [1//2, 0] => 4, [1//2, 1//2] => 4, [1//3, 1//3] => 6, [2//3, 2//3] => 6)
    @test Dict(p.u => length(p.stabilizer) for p in sp) == expected
    # orbits: {(1,1,1)}, the three points of order two, and the pair with zeta
    @test sort([p.orbit for p in sp]) == [1, 2, 2, 3, 3, 3]
    @test count(p -> p.rep, sp) == 3
    # the stabilizers: G, the Klein group (abelian of order 4) and S3 (nonabelian of order 6)
    G = act.G
    for p in sp
        S, _ = sub(G, p.stabilizer)
        if length(p.stabilizer) == 12
            @test order(S) == 12
        elseif length(p.stabilizer) == 4
            @test is_abelian(S) && all(x -> order(x) <= 2, p.stabilizer)
        else
            @test !is_abelian(S) && order(S) == 6
        end
    end
    # the six curves are the fixed curves of the six reflections: two orbits of three under conjugation
    layers = [c.layer for c in fc]
    function orbit_of(l)
        out = Set{typeof(l)}()
        for (g, f) in act.images
            # g maps the layer {m . u = c} to {m (nu^-1 u) = c} = {(m nu^-1) . u = c}, with the translation zero here
            ninv = Int.(round.(inv(f.nu)))
            mm = vec(l.m' * ninv)
            push!(out, FixedLayer(mm, l.c))
        end
        out
    end
    orbs = Set(orbit_of(l) for l in layers)
    @test sort([length(o) for o in orbs]) == [3, 3]
end

@testset "reflections with translations: the generic stabilizer of a curve uses the translation part" begin
    # G generated by the swap s and the translation by (1/2, 0). Its conjugate by s is the translation by (0, 1/2), so the group
    # has order 8. The curve u1 = u2 is fixed pointwise by s only, the curve u1 - u2 = 1/2 by the swap composed with the translation
    # by (1/2, 1/2) only.
    swap = AffineTorusMap([0 1; 1 0], [0, 0])
    tau = AffineTorusMap(I2, [1//2, 0])
    act = ToricAction([swap, tau], toric_fan_P2())
    @test order(act.G) == 8
    fc = fixed_curves(act)
    @test length(fc) == 2 && all(c -> length(c.H) == 2, fc)
    @test Set(c.layer for c in fc) == Set([FixedLayer([1, -1], 0), FixedLayer([1, -1], 1//2)])
    # the translations alone fix no curve and no point
    @test isempty(fixed_curves(ToricAction([tau], toric_fan_P2())))
end

@testset "special points of the monomial action (7.1) with n = 8" begin
    maps = [AffineTorusMap(I2, [1//8, 0]), AffineTorusMap(I2, [0, 7//8]), AffineTorusMap(NUC, [0, 0])]
    act = ToricAction(maps, toric_fan_P2())
    @test isempty(fixed_curves(act))                         # no reflections, no fixed curves
    sp = special_points(act)
    @test length(sp) == 192 && all(p -> length(p.stabilizer) == 3 && p.orbit == 64, sp)
    @test count(p -> p.rep, sp) == 3                         # the three orbits of points with stabilizer C3
end

end
