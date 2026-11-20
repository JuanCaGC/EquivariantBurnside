module TestToricGlide
using Test, Oscar, EquivariantBurnside

const SQ = [[1, 0], [0, 1], [-1, 0], [0, -1]]
refl = [1 0; 0 -1]
I2 = [1 0; 0 1]

# A glide reflection f = (refl, (1/2, b)) with b not zero has no fixed curve, since the first coordinate of
# (nu - I) u is zero while the translation has first coordinate 1/2. On the boundary divisor x = 0 (coordinate
# y = exp(2 pi i u2)) the map is x -> -x, y -> exp(2 pi i b) / y. Its two fixed points y^2 = exp(2 pi i b) have
# weights (-1, -1), an isolated scalar fixed point of order two, so each is blown up and gives one exceptional
# divisor with H = <f> and weight 1. The same happens on x = infinity. These are four G-orbits (G has order two),
# four symbols (C2, C2, 1). In BC_2 they are all zero (H of order two), so the test works with the formal terms.
# This case was found by a mutation of the code that finds the boundary points, which the earlier tests did not detect.
@testset "glide reflection without fixed curves, boundary fixed points" begin
    for b in (1 // 5, 1 // 3, 2 // 7)
        act = ToricAction([AffineTorusMap(refl, [1 // 2, b])], SQ)
        @test isempty(fixed_curves(act))
        cls = toric_class(act; points = true)
        @test sum(c for (c, _) in cls.terms) == 4
        @test length(cls.terms) == 4
        for (c, s) in cls.terms
            @test c == 1
            @test length(s.hg) == 1 && Int(GAP.Globals.Order(s.hg[1])) == 2
            @test s.betas == [[1]]
            @test Int(GAP.Globals.Size(GAP.Globals.Group(GAP.GapObj(vcat(s.hg, s.yg))))) == 2
        end
        # the group has reflection type elements, so the points cannot be switched off
        @test_throws ArgumentError toric_class(act; points = false)
    end
    # the translation (1/2, 0) alone is also a glide without fixed curves, with fixed points w = 0 and 1/2 on the boundary,
    # while a reflection with translation (0, 1/5) along its fixed direction does have fixed curves
    act0 = ToricAction([AffineTorusMap(refl, [1 // 2, 0 // 1])], SQ)
    @test isempty(fixed_curves(act0))
    @test length(toric_class(act0; points = true).terms) == 4
    actr = ToricAction([AffineTorusMap(refl, [0 // 1, 1 // 5])], SQ)
    @test !isempty(fixed_curves(actr))
end
end
