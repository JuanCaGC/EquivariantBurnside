module TestProjectiveLine
using Test, Oscar, EquivariantBurnside

function throws(phrase, f)
    try
        f()
    catch e
        return e isa ArgumentError && occursin(phrase, e.msg)
    end
    return false
end

zeta(n, k = 1) = exp(2im * pi * k / n)
diagm2(a, b) = Matrix{ComplexF64}([a 0; 0 b])
const SWAP = Matrix{ComplexF64}([0 1; 1 0])

# the triangle group (2, 3, n) inside PGL_2: a = z -> zeta_n^k z, b = [[1,1],[r,-1]] with r = 1 - 2 cos(2 pi k / n),
# so that b has order 2 and a b has order 3 (tr^2 / det = 1)
function triangle(G, a, b, n, k)
    r = 1 - 2cos(2pi * k / n)
    return ProjAction(G, [diagm2(zeta(n, k), 1), Matrix{ComplexF64}([1 1; r -1])]; gens = [a, b])
end

# an involution b with <a, b> = G and a b of order 3
function find_b(G, a)
    for x in G
        order(x) == 2 && order(a * x) == 3 && order(sub(G, [a, x])[1]) == order(G) && return x
    end
    error("no generator found")
end

@testset "projective line actions and class in BC_1" begin
    @testset "cyclic groups: two points, weights zeta^k and zeta^-k" begin
        for (n, k) in ((5, 1), (5, 2), (7, 3), (6, 1), (9, 2))
            G = cyclic_group(PermGroup, n)
            g = gen(G, 1)
            act = ProjAction(G, [diagm2(zeta(n, k), 1)])
            cls = projective_line_class(act)
            @test length(cls.terms) == 2
            expected = BCClass(G, 1)
            push!(expected, BCSymbol(G, [g], [], [[mod(k, n)]]))
            push!(expected, BCSymbol(G, [g], [], [[mod(-k, n)]]))
            @test bc_image(cls) == bc_image(expected)
        end
        # sensitivity: the sign of the weight and the value k matter in BC_1(C_7)
        G = cyclic_group(PermGroup, 7)
        g = gen(G, 1)
        c(k) = bc_image(projective_line_class(ProjAction(G, [diagm2(zeta(7, k), 1)])))
        @test c(1) == c(6)                      # k and -k: the same up to conjugation in PGL_2, the same class
        @test c(1) != c(2)
        @test c(1) != c(3)
        @test c(2) != c(3)
        wrong = BCClass(G, 1)                   # the two weights counted with the same sign are a different class
        push!(wrong, BCSymbol(G, [g], [], [[1]]))
        push!(wrong, BCSymbol(G, [g], [], [[1]]))
        @test bc_image(wrong) != c(1)
    end

    @testset "the datum of cyclic and dihedral actions" begin
        G = cyclic_group(PermGroup, 7)
        g = gen(G, 1)
        d(k) = pgl2_datum(ProjAction(G, [diagm2(zeta(7, k), 1)]))
        @test d(1)[g] == 1 // 7
        @test d(2)[g] == 2 // 7
        @test d(3)[g] == 3 // 7
        @test d(6)[g] == 1 // 7                 # theta is defined modulo sign
        @test d(1)[g^2] == 2 // 7
        @test d(1)[g^3] == 3 // 7
        @test d(1)[g^4] == 3 // 7
        @test d(1)[one(G)] == 0
        # dihedral groups D_m = <r, s>, the involutions have ratio of eigenvalues -1
        for m in (3, 4, 5, 7)
            G = dihedral_group(PermGroup, 2m)
            r, s = gens(G)
            act = ProjAction(G, [diagm2(zeta(m), 1), SWAP]; gens = [r, s])
            dt = pgl2_datum(act)
            @test dt[s] == 1 // 2
            @test dt[r] == 1 // m
            @test all(dt[r^j * s] == 1 // 2 for j in 0:m-1)
        end
    end

    @testset "datum is invariant under conjugation in PGL_2 and detects the embedding" begin
        P = [1.0+0.5im 0.3; -0.2im 2.0]
        G = cyclic_group(PermGroup, 5)
        for k in (1, 2)
            act = ProjAction(G, [diagm2(zeta(5, k), 1)])
            @test pgl2_datum(pgl2_conjugate(act, P)) == pgl2_datum(act)
            @test bc_image(projective_line_class(pgl2_conjugate(act, P))) == bc_image(projective_line_class(act))
        end
        a1 = ProjAction(G, [diagm2(zeta(5, 1), 1)])
        a2 = ProjAction(G, [diagm2(zeta(5, 2), 1)])
        @test pgl2_datum(a1) != pgl2_datum(a2)
        # D_5: the two faithful actions r -> zeta^1 and r -> zeta^2 have different data and different classes
        D = dihedral_group(PermGroup, 10)
        r, s = gens(D)
        e(k) = ProjAction(D, [diagm2(zeta(5, k), 1), SWAP]; gens = [r, s])
        @test pgl2_datum(e(1)) != pgl2_datum(e(2))
        @test bc_image(projective_line_class(e(1))) != bc_image(projective_line_class(e(2)))
        @test pgl2_datum(e(1)) == pgl2_datum(e(4))
        @test bc_image(projective_line_class(e(1))) == bc_image(projective_line_class(e(4)))
    end

    @testset "A4, S4 and A5: stabilizer orders and the two actions of A5" begin
        # A4, orbits with stabilizers C3 and C3 (weights 1 and 2) and C2
        G = alternating_group(4)
        a = cperm(G, [1, 2, 3])
        b = find_b(G, a)
        act = triangle(G, a, b, 3, 1)
        cls = projective_line_class(act)
        @test length(cls.terms) == 3
        expected = BCClass(G, 1)
        push!(expected, BCSymbol(G, [a], [], [[1]]))
        push!(expected, BCSymbol(G, [a], [], [[2]]))
        push!(expected, BCSymbol(G, [b], [], [[1]]))
        @test bc_image(cls) == bc_image(expected)
        # S4
        G = symmetric_group(4)
        a = cperm(G, [1, 2, 3, 4])
        b = find_b(G, a)
        cls = projective_line_class(triangle(G, a, b, 4, 1))
        @test sort([Int(GAP.Globals.Order(s.hg[1])) for (_, s) in cls.terms]) == [2, 3, 4]
        # A5, the printed example: the two actions differ at the vertices of the icosahedron only
        G = alternating_group(5)
        a = cperm(G, [1, 2, 3, 4, 5])
        b = find_b(G, a)
        c1 = projective_line_class(triangle(G, a, b, 5, 1))
        c2 = projective_line_class(triangle(G, a, b, 5, 2))
        @test length(c1.terms) == 3 && length(c2.terms) == 3
        @test sort([Int(GAP.Globals.Order(s.hg[1])) for (_, s) in c1.terms]) == [2, 3, 5]
        x1, x2 = bc_image(c1), bc_image(c2)
        @test x1 != x2
        hand = BCClass(G, 1)
        push!(hand, BCSymbol(G, [a], [], [[1]]))
        push!(hand, -1, BCSymbol(G, [a], [], [[2]]))
        @test x1 - x2 == bc_image(hand)
        @test pgl2_datum(triangle(G, a, b, 5, 1)) != pgl2_datum(triangle(G, a, b, 5, 2))
        @test bc_image(projective_line_class(triangle(G, a, b, 5, 1))) == bc_image(projective_line_class(triangle(G, a, b, 5, 4)))
        @test pgl2_datum(triangle(G, a, b, 5, 1)) == pgl2_datum(triangle(G, a, b, 5, 4))
    end

    @testset "right convention and errors" begin
        G = symmetric_group(3)
        r = diagm2(zeta(3), 1)
        gs = [cperm(G, [1, 2, 3]), perm(G, [2, 1, 3])]
        act = ProjAction(G, [r, SWAP]; gens = gs)
        @test Int(order(act.G)) == 6
        # a non homomorphism: the images of a rotation and a swap with the wrong relation
        @test throws("homomorphism", () -> ProjAction(G, [r, diagm2(zeta(5), 1)]; gens = gs))
        # not faithful
        @test throws("faithful", () -> ProjAction(G, [diagm2(1, 1) * 1.0, diagm2(1, 1) * 1.0]; gens = gs))
        @test throws("generate", () -> ProjAction(G, [r]; gens = [cperm(G, [1, 2, 3])]))
        @test throws("one matrix", () -> ProjAction(G, [r]; gens = gs))
        @test throws("singular", () -> ProjAction(G, [Matrix{ComplexF64}([1 1; 1 1]), SWAP]; gens = gs))
        @test throws("convention", () -> ProjAction(G, [r, SWAP]; gens = gs, convention = :up))
        @test throws("2 by 2", () -> ProjAction(G, [ones(3, 3), SWAP]; gens = gs))
        @test throws("singular", () -> pgl2_conjugate(act, [1 1; 1 1]))
        # the product a * b of G is the matrix r s for the left convention and s r for the right convention
        a, b = gs
        al = ProjAction(G, [r, SWAP]; gens = gs, convention = :left)
        ar = ProjAction(G, [r, SWAP]; gens = gs, convention = :right)
        pm(A, B) = EquivariantBurnside._pm_equal(A, B)
        @test !pm(r * SWAP, SWAP * r)
        @test pm(al.mats[a * b], r * SWAP) && !pm(al.mats[a * b], SWAP * r)
        @test pm(ar.mats[a * b], SWAP * r) && !pm(ar.mats[a * b], r * SWAP)
        # abelian groups do not see the convention, and the class does not depend on it
        C = cyclic_group(PermGroup, 5)
        l = ProjAction(C, [diagm2(zeta(5, 2), 1)]; convention = :left)
        rr = ProjAction(C, [diagm2(zeta(5, 2), 1)]; convention = :right)
        @test pgl2_datum(l) == pgl2_datum(rr)
        @test bc_image(projective_line_class(l)) == bc_image(projective_line_class(rr))
    end
end
end
