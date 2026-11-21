module TestRecursion
using Test, Oscar, EquivariantBurnside, LinearAlgebra
import EquivariantBurnside: DCP

const GGl = Oscar.GAP.Globals
firstsym(cls) = first(values(cls.terms))[2]

Oscar.GAP.evalstr("""
EB_SmallFaithful2 := function(o, i)
  local G, chi, rep, gens;
  G := SmallGroup(o, i);
  chi := First(Irr(G), c -> c[1] = 2 and Size(KernelOfCharacter(c)) = 1);
  if chi = fail then return fail; fi;
  rep := IrreducibleRepresentationsDixon(G, chi);
  gens := List(GeneratorsOfGroup(G), g -> Image(rep, g));
  return Group(gens);
end;
EB_ToC := function(c)
  local N;
  N := Conductor(c);
  return [N, CoeffsCyc(c, N)];
end;
EB_StdMat := function(n, p)
  local M, i, v, j;
  M := [];
  for i in [1..n-1] do
    v := List([1..n], j -> 0); v[i^p] := 1; v[n^p] := v[n^p] - 1;
    Add(M, v{[1..n-1]});
  od;
  return M;
end;
EB_Order := function(c) return Order(c); end;
""")

function tocomplex(M)
    n = Int(GGl.Length(M))
    out = zeros(ComplexF64, n, n)
    for i in 1:n, j in 1:n
        v = GGl.EB_ToC(M[i][j])
        N = Int(v[1])
        co = [x isa Integer ? Float64(x) : Int(GGl.NumeratorRat(x)) / Int(GGl.DenominatorRat(x)) for x in v[2]]      # the coefficients may be rational
        out[i, j] = sum(co[k + 1] * cis(2pi * k / N) for k in 0:(N - 1))
    end
    return out
end

gapgroup(s) = GGl.Group(Oscar.GAP.evalstr(s))
cyc(n, exps...) = gapgroup("[ [" * join(["[" * join([i == j ? "E($n)^$(exps[i])" : "0" for j in 1:length(exps)], ",") * "]" for i in 1:length(exps)], ",") * "] ]")
dih(n) = gapgroup("[ [[E($n),0],[0,E($n)^-1]], [[0,1],[1,0]] ]")

# the image of the class of P(V) in BC_1(G/C), for dim V = 2, compared with the projective line class of Phase 5
function v1_equal(Ggap)
    rep = linrep(Ggap)
    out, Q, proj, dropped = indexed_eta(projective_class(rep), rep.C)
    gP = Any[g for g in gens(rep.P)]
    act = ProjAction(Q, [tocomplex(rep.mats[g]) for g in gP]; gens = [proj(g) for g in gP])
    return bc_image(out) == bc_image(projective_line_class(act)), length(rep.C)
end


Oscar.GAP.evalstr("EB_Plus := function(M) return [[1,0,0],[0,M[1][1],M[1][2]],[0,M[2][1],M[2][2]]]; end;")
Oscar.GAP.evalstr("EB_Conj := function(T, M) return T^-1 * M * T; end;")
Oscar.GAP.evalstr("EB_Twist := function(chi, M) return chi * M; end;")

# the map of the permutation groups of two representations of the same abstract group, given by the matrices of the images
function rep_map(rep1, rep2, matfun)
    gP = Any[g for g in gens(rep1.P)]
    imgs = Any[EquivariantBurnside._matrix_to_element(rep2, matfun(rep1.mats[g])) for g in gP]
    return hom(rep1.P, rep2.P, gP, imgs)
end

Oscar.GAP.evalstr("EB_TwistDet := function(M) return DeterminantMat(M) * M; end;")

# true when the images in BC of the classes of P(V) for two representations of the same abstract group agree after transport
# along the map of the permutation groups defined by the matrices
function bc_equal_under(rep1, rep2, matfun)
    out1, Q1, pr1 = projective_bc_class(rep1)
    out2, Q2, pr2 = projective_bc_class(rep2)
    f = rep_map(rep1, rep2, matfun)
    lift(rep, pr, q) = length(rep.C) == 1 ? q : Oscar.preimage(pr, q)
    gq = Any[q for q in gens(Q1)]
    imgs = Any[pr2(f(lift(rep1, pr1, q))) for q in gq]
    phi = hom(Q1, Q2, gq, imgs)
    return bc_image(bc_transport(out1, phi)) == bc_image(out2), order(bc_image(out2))
end

function monomial_affine(rep, M)
    n = 3
    sigma = zeros(Int, n)
    a = zeros(Rational{Int}, n)
    for i in 1:n
        j = findfirst(jj -> !iszero(M[i][jj]), 1:n)
        sigma[i] = j
        c = M[i][j]
        m = Int(GGl.EB_Order(c))
        a[i] = m == 1 ? 0 // 1 : (Int(GGl.EB_CycExp(c, m)) // m)
    end
    k = findfirst(==(3), sigma)
    Nm = zeros(Int, 2, 2)
    t = zeros(Rational{Int}, 2)
    for i in 1:n
        j = sigma[i]
        j == 3 && continue
        i <= 2 && (Nm[j, i] += 1)
        k <= 2 && (Nm[j, k] -= 1)
        t[j] = a[i] - a[k]
    end
    return AffineTorusMap(Nm, [t[1], t[2]])
end

function v3_equal(Ggap)
    rep = linrep(Ggap)
    out, Q, proj, dropped = indexed_eta(projective_class(rep), rep.C)
    qgens = Any[q for q in gens(Q)]
    maps = AffineTorusMap[]
    for q in qgens
        g = rep.C == [one(rep.P)] ? q : Oscar.preimage(proj, q)
        push!(maps, monomial_affine(rep, rep.mats[g]))
    end
    act = ToricAction(Q, maps, toric_fan_P2(); convention = :right)
    return bc_image(out) == bc_image(toric_class(act)), order(bc_image(out)), length(rep.C)
end

@testset "recursion of Kresch and Tschinkel for P(V)" begin
    @testset "V1: dimension two against the projective line class of Phase 5" begin
        cases = [
            ("C5 diag(z,1)", cyc(5, 1, 0)),
            ("C6 diag(z,z^3)", cyc(6, 1, 3)),
            ("C4 scalar", cyc(4, 1, 1)),
            ("C7 diag(z,z^3)", cyc(7, 1, 3)),
            ("C12 diag(z,z^5)", cyc(12, 1, 5)),
            ("S3 standard", DCP.standard_symmetric(3)),
            ("D4", dih(4)),
            ("D5", dih(5)),
            ("D6", dih(6)),
        ]
        for (name, G) in cases
            eq, nsc = v1_equal(G)
            @test eq
        end
        for (o, i) in ((8, 4), (24, 3), (48, 28), (120, 5))
            G = GGl.EB_SmallFaithful2(o, i)
            @test G != GGl.fail
            eq, nsc = v1_equal(G)
            @test eq
            @test nsc == 2                  # the binary groups contain the scalar -1
        end
    end

    @testset "the generic term and the scalar character" begin
        # G = <diag(i, i)> is scalar, P(V) = P^1 with the trivial action: one symbol (C in C, G/C acting on k(t), (), epsilon)
        rep = linrep(cyc(4, 1, 1))
        cls = projective_class(rep)
        @test length(cls) == 1 && length(rep.C) == 4
        s = firstsym(cls)
        g = first(x for x in gens(rep.P))
        @test s.d == 1 && length(s.A) == 4 && length(s.H) == 4 && isempty(s.beta)
        # the eigenvalue of diag(i, i) is i = exp(2 pi i / 4) and epsilon is the eigenvalue, not its inverse
        @test s.gamma[0][g] == 1 // 4
        @test s.gamma[0][g^3] == 3 // 4
        # the trivial group in dimension one is a point with the generic symbol only
        rep1 = linrep(cyc(3, 1))
        c1 = projective_class(rep1)
        @test length(c1) == 1 && firstsym(c1).d == 0 && firstsym(c1).gamma[0][first(gens(rep1.P))] == 1 // 3
    end

    @testset "V2: the standard representation of S4 (Proposition 9.4 of KT-repr)" begin
        G = DCP.standard_symmetric(4)
        rep = linrep(G)
        P = rep.P
        cls = projective_class(rep)
        el(s) = EquivariantBurnside._matrix_to_element(rep, GGl.EB_StdMat(4, Oscar.GAP.evalstr(s)))
        a12, a34, a123, a1234 = el("(1,2)"), el("(3,4)"), el("(1,2,3)"), el("(1,2,3,4)")
        d1, d2 = el("(1,2)(3,4)"), el("(1,3)(2,4)")
        chr(gs, ex) = indexed_character(P, gs, ex)
        zer(gs) = chr(gs, [0 for _ in gs])
        mk(A, Y, d, beta, gam) = IndexedSymbol(P, [], A, Y, d, beta, Dict(0 => gam))
        e(u, v) = chr([a12, a34], [u, v])
        k(u, v) = chr([d1, d2], [u, v])
        D4 = [a12, a34, d2]
        # the 16 terms of the last display of the proof of Proposition 9.4, before applying eta
        want = IndexedClass(P, 3, [0])
        push!(want, mk([], Any[g for g in gens(P)], 2, [], Dict(one(P) => 0 // 1)))
        push!(want, mk([a12], [a12], 0, [chr([a12], [1]), chr([a12], [1])], zer([a12])))
        push!(want, mk([a123], [a123], 0, [chr([a123], [1]), chr([a123], [1])], zer([a123])))
        push!(want, mk([a12], [a12, a34], 1, [chr([a12], [1])], zer([a12])))
        push!(want, mk([a1234], [a1234], 0, [chr([a1234], [2]), chr([a1234], [3])], chr([a1234], [2])))
        push!(want, mk([d1], D4, 1, [chr([d1], [1])], zer([d1])))
        push!(want, mk([d1], D4, 1, [chr([d1], [1])], chr([d1], [1])))
        push!(want, mk([a12], [a12, a34], 1, [chr([a12], [1])], chr([a12], [1])))
        push!(want, mk([a123], [a123], 0, [chr([a123], [1]), chr([a123], [1])], chr([a123], [1])))
        push!(want, mk([a123], [a123], 0, [chr([a123], [2]), chr([a123], [2])], chr([a123], [1])))
        push!(want, mk([a1234], [a1234], 0, [chr([a1234], [1]), chr([a1234], [1])], chr([a1234], [1])))
        push!(want, mk([a12, a34], [a12, a34], 0, [e(0, 1), e(1, 1)], e(0, 0)))
        push!(want, mk([d1, d2], [d1, d2], 0, [k(1, 0), k(0, 1)], k(0, 1)))
        push!(want, mk([a1234], [a1234], 0, [chr([a1234], [2]), chr([a1234], [3])], chr([a1234], [1])))
        push!(want, mk([a12, a34], [a12, a34], 0, [e(1, 0), e(0, 1)], e(1, 0)))
        push!(want, mk([a12, a34], [a12, a34], 0, [e(1, 1), e(0, 1)], e(1, 0)))
        @test length(cls) == 16 && length(want) == 16
        @test cls == want
        # level 1: eta, then the statement of Proposition 9.4 in BC_2(S4)
        out, Q, proj, dropped = indexed_eta(cls, rep.C)
        @test dropped == 1
        st = BCClass(P, 2)
        push!(st, 1, BCSymbol(P, [a12], [a12, a34], [[1]]))
        push!(st, 2, BCSymbol(P, [d1], [a12, a34, d2], [[1]]))
        push!(st, 2, BCSymbol(P, [a12, a34], Any[], [[1, 0], [1, 1]]))
        push!(st, 1, BCSymbol(P, [d1, d2], Any[], [[1, 0], [0, 1]]))
        push!(st, 1, BCSymbol(P, [a123], Any[], [[1], [1]]))
        push!(st, 2, BCSymbol(P, [a1234], Any[], [[1], [2]]))
        @test bc_image(out) == bc_image(st)
        @test !iszero(bc_image(out))
        # the third oracle: the toric class of the monomial presentation (signed permutations), same group, right action
        I2 = [1 0; 0 1]
        NUC = [0 -1; 1 -1]
        SW = [0 1; 1 0]
        maps = [AffineTorusMap(I2, [1 // 2, 0]), AffineTorusMap(I2, [0, 1 // 2]), AffineTorusMap(NUC, [0, 0]), AffineTorusMap(SW, [0, 0])]
        tact = ToricAction(maps, toric_fan_P2())
        tc = toric_class(tact)
        phi = isomorphism(Q, tact.G)
        @test bc_image(bc_transport(out, phi)) == bc_image(tc)
    end
    @testset "V3: monomial actions on P^2 against toric_class (same group, right action)" begin
        CYCP = "[[0,1,0],[0,0,1],[1,0,0]]"
        SWP = "[[0,1,0],[1,0,0],[0,0,1]]"
        dg(n, a, b, c) = "[[E($n)^$a,0,0],[0,E($n)^$b,0],[0,0,E($n)^$c]]"
        cases = [
            ("C5", "[" * dg(5, 1, 2, 0) * "]"),
            ("C8", "[" * dg(8, 1, 3, 0) * "]"),
            ("C2xC2", "[" * dg(2, 1, 0, 0) * "," * dg(2, 0, 1, 0) * "]"),
            ("C3xC3", "[" * dg(3, 1, 0, 0) * "," * dg(3, 0, 1, 0) * "]"),
            ("C6 with scalar C3", "[" * dg(6, 1, 1, 4) * "]"),
            ("C3 scalar and C4", "[" * dg(3, 1, 1, 1) * "," * dg(4, 1, 0, 0) * "]"),
            ("C7 : C3", "[" * dg(7, 1, 2, 4) * "," * CYCP * "]"),
            ("S3 permutations", "[" * CYCP * "," * SWP * "]"),
            ("C3 cyclic permutation", "[" * CYCP * "]"),
            ("Heisenberg", "[" * dg(3, 0, 1, 2) * "," * CYCP * "]"),
            ("S4 signed permutations", "[" * dg(2, 1, 1, 0) * "," * dg(2, 0, 1, 1) * "," * CYCP * "," * SWP * "]"),
            ("A4 monomial", "[" * dg(2, 1, 1, 0) * "," * dg(2, 0, 1, 1) * "," * CYCP * "]"),
            ("C4 and C3 permutation", "[" * dg(4, 1, 0, 0) * "," * CYCP * "]"),
        ]
        nonzero = 0
        for (name, s) in cases
            eq, ord, nsc = v3_equal(gapgroup(s))
            @test eq
            nonzero += ord > 1
        end
        @test nonzero >= 4          # the comparison is not only between zero classes
    end

    @testset "V4: invariance under a change of basis and under a twist by a character" begin
        G = DCP.standard_symmetric(4)
        rep = linrep(G)
        T = Oscar.GAP.evalstr("[[1,1,0],[0,1,2],[1,0,1]]")
        G2 = GGl.Group(Oscar.GAP.GapObj([GGl.EB_Conj(T, g) for g in GGl.GeneratorsOfGroup(G)]))
        rep2 = linrep(G2)
        # the formal class at level 0 is the same after transport (it does not depend on the basis)
        f = rep_map(rep, rep2, M -> GGl.EB_Conj(T, M))
        cls = projective_class(rep)
        cls2 = projective_class(rep2)
        @test length(cls) == 16
        @test indexed_induce(cls, rep2.P, x -> f(x)) == cls2
        # twisting S4 by the determinant (the sign) does not change the projective action
        G3 = GGl.Group(Oscar.GAP.GapObj([GGl.EB_TwistDet(g) for g in GGl.GeneratorsOfGroup(G)]))
        rep3 = linrep(G3)
        eq, ord = bc_equal_under(rep, rep3, M -> GGl.EB_TwistDet(M))
        @test eq && ord == 2
        # dimension two with a scalar subgroup: the binary octahedral group, and a cyclic group twisted by its determinant
        B = GGl.EB_SmallFaithful2(48, 28)
        T2 = Oscar.GAP.evalstr("[[1,2],[0,1]]")
        B2 = GGl.Group(Oscar.GAP.GapObj([GGl.EB_Conj(T2, g) for g in GGl.GeneratorsOfGroup(B)]))
        eq, ord = bc_equal_under(linrep(B), linrep(B2), M -> GGl.EB_Conj(T2, M))
        @test eq
        C12 = cyc(12, 1, 5)
        C12t = GGl.Group(Oscar.GAP.GapObj([GGl.EB_TwistDet(g) for g in GGl.GeneratorsOfGroup(C12)]))
        eq, ord = bc_equal_under(linrep(C12), linrep(C12t), M -> GGl.EB_TwistDet(M))
        @test eq
        # a representation with a nontrivial scalar subgroup in dimension three, twisted
        Hz = gapgroup("[ [[E(3),0,0],[0,E(3),0],[0,0,E(3)]], [[0,1,0],[0,0,1],[1,0,0]], [[1,0,0],[0,E(3),0],[0,0,E(3)^2]] ]")
        Hzt = GGl.Group(Oscar.GAP.GapObj([GGl.EB_TwistDet(g) for g in GGl.GeneratorsOfGroup(Hz)]))
        eq, ord = bc_equal_under(linrep(Hz), linrep(Hzt), M -> GGl.EB_TwistDet(M))
        @test eq
    end

    @testset "dimension four smoke test: S5 on the standard representation" begin
        # no oracle exists here, the checks are the structure found independently by Codex (35 chains modulo G, 804 flags,
        # 76 N-orbits of strict extensions) and that every symbol produced passes the validation of IndexedSymbol
        rep = linrep(DCP.standard_symmetric(5))
        chs = DCP.chains(rep.arr)
        flags, lookup, rep_of = EquivariantBurnside._flag_data(rep, chs)
        @test length(chs) == 35 && length(flags) == 804
        cls = projective_class(rep)
        @test length(cls) == 55 && sum(c for (_, (c, s)) in cls.terms) == 64      # a regression value, not an oracle
        @test cls.n == 4 && cls.I == [0]
        out, Q, proj = projective_bc_class(rep)
        @test out.n == 3
    end

    @testset "V5: P(1 + V) of Theorem 8.5 against toric_class for dim V = 2" begin
        function v5(G2)
            rep = linrep(G2)
            out = projective_plus_bc_class(rep)
            maps = AffineTorusMap[monomial_affine(rep, GGl.EB_Plus(rep.mats[g])) for g in gens(rep.P)]
            act = ToricAction(rep.P, maps, toric_fan_P2(); convention = :right)
            return bc_image(out) == bc_image(toric_class(act)), order(bc_image(out))
        end
        nonzero = 0
        for G2 in (cyc(5, 1, 2), cyc(8, 1, 3), dih(3), dih(4), dih(5), cyc(7, 1, 3), cyc(12, 1, 5),
                   cyc(4, 1, 1), cyc(6, 1, 1), cyc(5, 2, 2), cyc(7, 3, 3))      # scalar subgroups of order > 2 detect the sign of epsilon
            eq, ord = v5(G2)
            @test eq
            nonzero += ord > 1
        end
        @test nonzero >= 4
        # Remark 8.6 with a trivial scalar subgroup: the number of terms with H trivial is the product with P^1, checked on one case
        rep = linrep(dih(5))
        pc = projective_plus_class(rep)
        @test !iszero(pc) && pc.n == 2 && isempty(pc.I)
        @test indexed_negate_gamma(indexed_negate_gamma(projective_class(rep))) == projective_class(rep)
    end
    @testset "Section 10 of KT-repr: the symbols (C_n, Gbar' acting on k(P(V)), +-eps) in P(1 + V_eps)" begin
        Oscar.GAP.evalstr("EB_ScalarId := function(z, n) return z * IdentityMat(n); end;")
        function twisted(Gp, n)
            d = Int(GGl.Length(GGl.One(Gp)))
            gs = vcat([GGl.EB_ScalarId(GGl.E(n), d)], [g for g in GGl.GeneratorsOfGroup(Gp)])
            return GGl.Group(Oscar.GAP.GapObj(gs))
        end
        function sec10(Gp, n)
            rep = linrep(twisted(Gp, n))
            pc = projective_plus_class(rep)
            zc = first(x for x in rep.C if order(x) == n)
            found = Dict{Rational{Int},Int}()
            for (_, (coef, s)) in pc.terms
                (length(s.A) == n && length(s.H) == 1 && length(s.Y) == Int(order(rep.P)) && s.d == rep.n - 1 &&
                 length(s.beta) == 1 && Set(s.A) == Set(rep.C)) || continue
                v = s.beta[1][zc]
                found[v] = get(found, v, 0) + coef
            end
            return found
        end
        # exactly the two symbols with beta = eps and beta = -eps, each with coefficient one
        @test sec10(DCP.standard_symmetric(3), 5) == Dict(1//5 => 1, 4//5 => 1)
        @test sec10(dih(5), 7) == Dict(1//7 => 1, 6//7 => 1)
    end
    @testset "field datum of the symbols (Phase 4.6)" begin
        # the projective invariant is the sorted list of ratios of eigenvalues, unchanged by a scalar
        M = Oscar.GAP.evalstr("[[1,0],[0,-1]]")
        @test projective_invariant(M) == [1 // 2, 1 // 2]
        @test projective_invariant(GGl.E(4) * M) == projective_invariant(M)
        @test projective_invariant(GGl.IdentityMat(3)) == zeros(Rational{Int}, 6)
        @test projective_invariant(Oscar.GAP.evalstr("[[0,1,0],[0,0,1],[1,0,0]]")) == sort([1 // 3, 1 // 3, 1 // 3, 2 // 3, 2 // 3, 2 // 3])
        # recording the field changes neither the number of terms nor the coefficients, and Y~/A acts faithfully on the field
        function fcheck(G)
            rep = linrep(G)
            c0 = projective_class(rep)
            cf = projective_class(rep; fields = true)
            ok, nofac, maxf = field_faithful(cf)
            @test ok
            @test length(cf.terms) == length(c0.terms)
            @test sum(c for (_, (c, _)) in cf.terms) == sum(c for (_, (c, _)) in c0.terms)
            return rep, cf, nofac, maxf
        end
        rep, cf, nofac, maxf = fcheck(DCP.standard_symmetric(4))
        @test (nofac, maxf) == (11, 1)
        for G2 in (dih(3), dih(5), cyc(8, 1, 3), GGl.EB_SmallFaithful2(24, 3))
            fcheck(G2)
        end
        # the printed field data of A4 acting on P^2: the generic term, then two terms with a P^1 and the points
        A4 = GGl.DerivedSubgroup(DCP.standard_symmetric(4))
        repA, cfA, _, _ = fcheck(A4)
        fp = Dict(field_fingerprint(cfA))
        @test fp[(1, 1, 12, 2, (0,), (), ((0, 1),), ((3, 12, 1),))] == 1
        @test fp[(1, 2, 4, 1, (0,), (2,), ((0, 1),), ((2, 2, 2),))] == 1
        @test fp[(1, 3, 3, 0, (0,), (3, 3), ((0, 3),), ())] == 4
        # invariance under a change of basis of V
        T = Oscar.GAP.evalstr("[[1,1,0],[0,1,0],[0,0,1]]")
        A4b = GGl.Group(Oscar.GAP.GapObj([GGl.Inverse(T) * g * T for g in GGl.GeneratorsOfGroup(A4)]))
        @test field_fingerprint(projective_class(linrep(A4b); fields = true)) == field_fingerprint(cfA)
        # omega adds a torus to the field and is refused on symbols that carry a field datum
        @test_throws ArgumentError indexed_omega(cfA, Int[])
    end
end
end
