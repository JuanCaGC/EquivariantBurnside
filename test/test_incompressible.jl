module TestIncompressible
using Test, Oscar, EquivariantBurnside

function throws(phrase, f)
    try
        f()
    catch e
        return e isa ArgumentError && occursin(phrase, e.msg)
    end
    return false
end

const I2 = [1 0; 0 1]
const SWAP = [0 1; 1 0]
const REFL = [1 0; 0 -1]
const REFL2 = [-1 0; 0 1]
const ROT4 = [0 -1; 1 0]
const NUC = [0 -1; 1 -1]
const SQ = [[1, 0], [0, 1], [-1, 0], [0, -1]]
const OCT = [[1, 0], [1, 1], [0, 1], [-1, 1], [-1, 0], [-1, -1], [0, -1], [1, -1]]
const A2FAN = [[1, 0], [0, 1], [-1, 1], [-1, 0], [0, -1], [1, -1]]
A(nu, t = [0, 0]) = AffineTorusMap(nu, t)

# C_n x D_m acting on P(1 + V_{eps, psi}): c = translation (a/n, a/n), r = translation (k/m, -k/m), s = swap
lin(n, a, m, k) = [A(I2, [a // n, a // n]), A(I2, [k // m, -k // m]), A(SWAP)]

genhom(a1, a2) = GAP.Globals.GroupHomomorphismByImages(GAP.GapObj(a1.G), GAP.GapObj(a2.G),
                     GAP.GapObj([GAP.GapObj(g) for g in a1.gens]), GAP.GapObj([GAP.GapObj(g) for g in a2.gens]))
function carry(a1, a2)
    f = genhom(a1, a2)
    f == GAP.Globals.fail && error("the generators do not define an isomorphism")
    return Oscar.GAPGroupHomomorphism(a1.G, a2.G, f)
end
# equality of the classes of two actions under the identification of the generators
same_ident(a1, c1, a2, c2) = inc_transport(c1, carry(a1, a2)) == c2

terms(c) = sort!([(t[1], length(t[2].H), length(t[2].Y)) for t in values(c.terms)])
thetas(s) = sort!(collect(values(s.theta)))
count_theta(s, x) = count(==(x), values(s.theta))

@testset "incompressible part of the class" begin
    @testset "hand derived: C2 x S3 on the A2 fan (Kresch-Tschinkel Proposition 6.1)" begin
        act = ToricAction([A(SWAP), A([0 1; -1 -1]), A(-I2)], A2FAN)
        c = incompressible_class(act)
        @test terms(c) == [(1, 2, 12)]
        s = first(values(c.terms))[2]
        # H = {1, -1} the scalars of the tangent plane, Y = S3 acts on P^1 with elements of order 1, 3, 2
        @test count_theta(s, 0 // 1) == 2
        @test count_theta(s, 1 // 3) == 4
        @test count_theta(s, 1 // 2) == 6
        @test all(==(1 // 2), [s.beta[h] for h in s.H if !isone(h)])
        # the linear action on P(1 + V_chi) has the same symbol with coefficient 2
        lina = ToricAction(lin(2, 1, 3, 1), toric_fan_P2())
        cl = incompressible_class(lina)
        @test terms(cl) == [(2, 2, 12)]
        ok, f = is_isomorphic_with_map(lina.G, act.G)
        @test ok
        # the two classes differ under every automorphism of G, as stated in Proposition 6.1 (the actions are not birational)
        @test inc_find_automorphism(cl, c, f) === nothing
        @test inc_find_automorphism(c, cl, inv(f)) === nothing
        @test !iszero(inc_transport(cl, f) - c)
    end

    @testset "hand derived: D4 on the square and two translations with a reflection" begin
        # D4 = <swap, refl>: the fixed points (0,0) and (1/2,1/2) have stabilizer D4, with scalars {+-1} and Y = D4 / {+-1} = V4
        d4 = ToricAction([A(SWAP), A(REFL)], SQ)
        c = incompressible_class(d4)
        @test terms(c) == [(2, 2, 8)]
        s = first(values(c.terms))[2]
        @test count_theta(s, 0 // 1) == 2 && count_theta(s, 1 // 2) == 6
        # a reflection with a translation of order 5 along the fixed direction: Y = G / C5 = C2 is cyclic, nothing
        @test iszero(incompressible_class(ToricAction([A(REFL), A(I2, [1 // 5, 0])], SQ)))
        # the extra translation (0, 1/2) makes Y = V4 on the divisors D_(1,0) and D_(-1,0) with H = C5 and weights +-1/5
        act5 = ToricAction([A(REFL), A(I2, [1 // 5, 0]), A(I2, [0, 1 // 2])], SQ)
        c5 = incompressible_class(act5)
        @test terms(c5) == [(1, 5, 20), (1, 5, 20)]
        ss = [t[2] for t in values(c5.terms)]
        @test all(s -> count_theta(s, 0 // 1) == 5 && count_theta(s, 1 // 2) == 15, ss)
        tau = act5.gens[2]
        @test sort([s.beta[tau] for s in ss]) == [1 // 5, 4 // 5]
        # D4 with translations of order 3: the divisors D_(1,0) and D_(1,1) have H = C3 and Y = S3
        d4t = ToricAction([A(SWAP), A(REFL), A(I2, [1 // 3, 0]), A(I2, [0, 1 // 3])], SQ)
        c7 = incompressible_class(d4t)
        @test length(c7) == 5
        t7 = terms(c7)
        @test count(t -> t[2] == 3 && t[3] == 18, t7) == 2      # the two orbits of rays, axes and diagonals
        @test (2, 2, 8) in t7                                      # (0,0) and (1/2,1/2) with Y = V4
    end

    @testset "no incompressible symbols: Example 7.5 and groups with cyclic Y" begin
        maps71(s, t, n) = [A(I2, [s // n, 0]), A(I2, [0, t // n]), A(NUC)]
        for (s, t, n) in ((1, 1, 8), (1, 3, 8), (1, 1, 5), (2, 1, 7))
            @test iszero(incompressible_class(ToricAction(maps71(s, t, n), toric_fan_P2())))
        end
        # a single reflection and the Klein group of reflections have only cyclic quotients
        @test iszero(incompressible_class(ToricAction([A(REFL)], SQ)))
        @test iszero(incompressible_class(ToricAction([A(REFL), A(REFL2)], SQ)))
        @test iszero(incompressible_class(ToricAction([A(I2, [1 // 7, 3 // 7])], toric_fan_P2())))
    end

    @testset "Corollary 7.7 and Lemma 7.8: C_n x D_m on P(1 + V)" begin
        n, m = 7, 5
        mk(a, k) = ToricAction(lin(n, a, m, k), toric_fan_P2())
        base = mk(1, 1)
        cb = incompressible_class(base)
        # the two symbols (C_n, D_m acting on k(P(V)), eps) and (C_n, D_m acting on k(P(V)), -eps)
        @test terms(cb) == [(1, n, 2 * m * n), (1, n, 2 * m * n)]
        ss = [t[2] for t in values(cb.terms)]
        c = base.gens[1]
        @test sort([s.beta[c] for s in ss]) == [1 // 7, 6 // 7]
        @test all(s -> thetas(s) == thetas(ss[1]), ss)
        # equal exactly for eps -> -eps and psi -> -psi
        for (a, k) in ((6, 1), (1, 4), (6, 4))
            @test same_ident(base, cb, mk(a, k), incompressible_class(mk(a, k)))
        end
        for (a, k) in ((2, 1), (3, 1), (1, 2), (2, 2), (3, 2))
            @test !same_ident(base, cb, mk(a, k), incompressible_class(mk(a, k)))
        end
        # sensitivity: for eps = eps' and psi != +-psi' the symbols have the same H, Y, beta and differ only in the datum
        other = mk(1, 2)
        co = incompressible_class(other)
        moved = inc_transport(cb, carry(base, other))
        strip(cls) = sort!([(t[1], sort!(string.(collect(t[2].H))), sort!(string.(collect(t[2].Y))),
                             sort!(collect(values(t[2].beta)))) for t in values(cls.terms)])
        @test strip(moved) == strip(co)
        @test moved != co
        # up to Aut(G) all of them are identified, the automorphism of C_n moving eps (the identity identification is the sharp one)
        @test inc_find_automorphism(cb, incompressible_class(mk(2, 1)), carry(base, mk(2, 1))) !== nothing
    end

    @testset "Example 7.9: C3 x D8, the two actions have the same incompressible part" begin
        mk(k) = ToricAction(lin(3, 1, 8, k), toric_fan_P2())
        a1, a3 = mk(1), mk(3)
        c1, c3 = incompressible_class(a1), incompressible_class(a3)
        @test order(a1.G) == 48
        # the printed incompressible symbols (C6, D4 acting on k(P^1), (1)) + (C6, D4 acting on k(P^1), (5))
        @test terms(c1) == [(1, 6, 48), (1, 6, 48)]
        s = first(values(c1.terms))[2]
        @test count_theta(s, 1 // 4) == 12 && count_theta(s, 1 // 2) == 30 && count_theta(s, 0 // 1) == 6
        cg = a1.gens[1]
        @test sort([t[2].beta[cg] for t in values(c1.terms)]) == [1 // 3, 2 // 3]
        @test same_ident(a1, c1, a3, c3)
        @test same_ident(a1, c1, mk(5), incompressible_class(mk(5)))
        # for n = 7 and m = 5 the characters psi and 3 psi are not equal up to sign and the classes are different
        b1, b3 = ToricAction(lin(7, 1, 5, 1), toric_fan_P2()), ToricAction(lin(7, 1, 5, 3), toric_fan_P2())
        @test !same_ident(b1, incompressible_class(b1), b3, incompressible_class(b3))
    end

    @testset "independence of the fan and of extra blowups" begin
        ex = [Rational{Int}[1//3, 1//3], Rational{Int}[1//2, 1//4], Rational{Int}[0, 1//5], Rational{Int}[1//2, 1//2], Rational{Int}[1//2, 0]]
        for maps in ([A(SWAP), A(REFL)],
                     [A(REFL), A(I2, [1 // 5, 0]), A(I2, [0, 1 // 2])],
                     [A(SWAP), A(REFL), A(I2, [1 // 3, 0]), A(I2, [0, 1 // 3])],
                     [A(ROT4), A(REFL), A(I2, [1 // 5, 0]), A(I2, [0, 1 // 5])])
            a4, a8 = ToricAction(maps, SQ), ToricAction(maps, OCT)
            c4, c8 = incompressible_class(a4), incompressible_class(a8)
            @test same_ident(a4, c4, a8, c8)
            @test incompressible_class(a4; extra_points = ex) == c4
            @test incompressible_class(a8; extra_points = ex) == c8
        end
        for maps in ([A(SWAP), A(I2, [1 // 2, 0])], [A(SWAP), A(I2, [1 // 5, 1 // 5])])
            a3, a6 = ToricAction(maps, toric_fan_P2()), ToricAction(maps, toric_fan_hexagon())
            @test same_ident(a3, incompressible_class(a3), a6, incompressible_class(a6))
        end
    end

    @testset "agreement with the divisor symbols of toric_class" begin
        # every incompressible symbol is a divisor symbol (H, Y, beta) of the class of toric_class, with the same
        # H, the same Y~ and the same character beta
        function found(act, s)
            G = act.G
            h0 = first(h for h in s.H if !isone(h) && order(h) == length(s.H))
            for (_, b) in toric_class(act).terms
                hs = Set(sub(G, [Oscar.group_element(G, x) for x in b.hg])[1])
                ys = Set(sub(G, [Oscar.group_element(G, x) for x in vcat(b.hg, b.yg)])[1])
                (hs == Set(s.H) && ys == Set(s.Y)) || continue
                hb = Oscar.group_element(G, b.hg[1])
                length(b.hg) == 1 || continue
                # beta(hb) from the character vector, hb = h0^j
                j = findfirst(j -> h0^j == hb, 1:length(s.H))
                j === nothing && continue
                x = j * s.beta[h0]
                x -= floor(x)
                x == b.betas[1][1] // b.ords[1] && return true
            end
            return false
        end
        cases = Any[
            ToricAction([A(SWAP), A([0 1; -1 -1]), A(-I2)], A2FAN),
            ToricAction([A(SWAP), A(REFL)], SQ),
            ToricAction([A(REFL), A(I2, [1 // 5, 0]), A(I2, [0, 1 // 2])], SQ),
            ToricAction([A(SWAP), A(REFL), A(I2, [1 // 3, 0]), A(I2, [0, 1 // 3])], SQ),
            ToricAction([A(ROT4), A(REFL), A(I2, [1 // 5, 0]), A(I2, [0, 1 // 5])], SQ),
            ToricAction(lin(7, 1, 5, 1), toric_fan_P2()),
            ToricAction(lin(3, 1, 8, 1), toric_fan_P2()),
            ToricAction(lin(2, 1, 3, 1), toric_fan_P2()),
        ]
        for act in cases
            c = incompressible_class(act)
            @test length(c) > 0
            @test all(found(act, t[2]) for t in values(c.terms))
        end
    end

    @testset "the algebra of classes" begin
        act = ToricAction([A(REFL), A(I2, [1 // 5, 0]), A(I2, [0, 1 // 2])], SQ)
        c = incompressible_class(act)
        @test length(c) == 2
        @test iszero(c - c)
        @test c + c == 2 * c
        @test iszero(c + (-c))
        @test iszero(0 * c)
        @test (-1) * c == -c
        @test c != 2 * c
        @test hash(c) == hash(incompressible_class(act))
        @test occursin("IncClass(2 symbols)", sprint(show, c))
        # conjugating a symbol by an element of G gives the same class
        s = first(values(c.terms))[2]
        for g in act.gens
            sg = IncSymbol(act.G, Any[x^g for x in s.H], Any[x^g for x in s.Y],
                           Dict{Any,Rational{Int}}(x^g => v for (x, v) in s.beta),
                           Dict{Any,Rational{Int}}(x^g => v for (x, v) in s.theta))
            d = copy(c)
            push!(d, -1, sg)
            @test length(d) == 1
        end
        # a symbol with another beta is a different generator
        wrong = IncSymbol(act.G, s.H, s.Y, Dict{Any,Rational{Int}}(h => 2 * v - floor(2 * v) for (h, v) in s.beta), s.theta)
        d = copy(c)
        push!(d, -1, wrong)
        @test length(d) == 3
        # errors
        other = ToricAction([A(REFL)], SQ)
        @test throws("different group", () -> push!(IncClass(other.G), s))
        @test throws("different groups", () -> c + IncClass(other.G))
        @test throws("different groups", () -> inc_find_automorphism(c, IncClass(other.G)))
    end

    @testset "transport along an isomorphism and along Aut(G)" begin
        act = ToricAction([A(SWAP), A(REFL), A(I2, [1 // 3, 0]), A(I2, [0, 1 // 3])], SQ)
        c = incompressible_class(act)
        # inner automorphisms act trivially
        g = act.gens[2]
        inn = hom(act.G, act.G, gens(act.G), [x^g for x in gens(act.G)])
        @test inc_transport(c, inn) == c
        psi = inc_find_automorphism(c, c)
        @test psi !== nothing
    end
end
end
