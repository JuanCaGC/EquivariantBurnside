module TestIndexed
using Test, Oscar, EquivariantBurnside, LinearAlgebra

function throws(phrase, f)
    try
        f()
    catch e
        return e isa ArgumentError && occursin(phrase, e.msg)
    end
    return false
end

zerochar(G, g) = indexed_character(G, [g], [0])

@testset "indexed symbols and the operations psi, tau, eta, induction" begin
    @testset "tau: the matrix and the action on the characters, derived by hand" begin
        # Example 4.1 of Kresch-Tschinkel: I = {0,1,2}, J = {0,2} sends (c0, c1, c2) to (c0, c1, c1 + c2)
        @test indexed_tau_matrix([0, 1, 2], [0, 2]) == [1 0 0; 0 1 1; 0 0 1]
        # J = {1,2}: index 0 is not kept and index 1 absorbs index 0
        @test indexed_tau_matrix([0, 1, 2], [1, 2]) == [1 1 0; 0 1 0; 0 0 1]
        # J = I and J = {0} (everything goes to 0, a retained index absorbs the earlier indices only)
        @test indexed_tau_matrix([0, 1, 2], [0, 1, 2]) == [1 0 0; 0 1 0; 0 0 1]
        @test indexed_tau_matrix([0, 1, 2], [0]) == [1 0 0; 0 1 0; 0 0 1]
        # J = {2}: index 2 absorbs 0, 1 and 2
        @test indexed_tau_matrix([0, 1, 2], [2]) == [1 0 1; 0 1 1; 0 0 1]
        # every matrix is unimodular, for all subsets of {0,..,4}
        for mask in 0:31
            I = [0, 1, 2, 3, 4]
            J = [i for i in I if (mask >> i) & 1 == 1]
            isempty(J) && continue
            @test abs(round(Int, det(indexed_tau_matrix(I, J)))) == 1
        end
        G = cyclic_group(PermGroup, 5)
        g = gen(G, 1)
        c(k) = indexed_character(G, [g], [k])
        # gamma = (c0, c1, c2) with exponents (1, 2, 4) modulo 5, so that every sum is visible
        for (J, want) in (([0, 2], [1, 2, 1]), ([1, 2], [1, 3, 4]), ([0, 1, 2], [1, 2, 4]), ([2], [1, 2, 2]), ([0, 1], [1, 2, 4]))
            cls = IndexedClass(G, 4, [0, 1, 2])
            push!(cls, IndexedSymbol(G, [], [g], [g], 0, [c(1)], Dict(0 => c(1), 1 => c(2), 2 => c(4))))
            out = indexed_tau(cls, J)
            s = first(values(out.terms))[2]
            @test [round(Int, 5 * s.gamma[i][g]) for i in 0:2] == want
        end
        @test throws("subset", () -> indexed_tau(IndexedClass(G, 4, [0, 1, 2]), [3]))
    end

    @testset "psi: Definition 4.2 on hand built symbols" begin
        G = cyclic_group(PermGroup, 12)
        g = gen(G, 1)
        a = g^3                                   # order 4
        ch(k) = indexed_character(G, [a], [k])    # a character of <a> by its value on a
        # A = <a>, H = <a^2> of order 2, beta = the character of order 2, gamma = four characters, three of them nonzero on A
        mk(gs) = IndexedSymbol(G, [a^2], [a], [a], 0, [ch(2)], Dict(i => ch(k) for (i, k) in enumerate(gs)))
        cls = IndexedClass(G, 5, [1, 2, 3, 4])
        push!(cls, mk([1, 2, 1, 3]))
        out = indexed_psi(cls, [1, 4])
        s = first(values(out.terms))[2]
        # the removed indices are 2 and 3 with characters ch(2) and ch(1): H becomes H intersect ker(ch(2)) intersect ker(ch(1))
        @test length(s.H) == 1 && length(s.A) == 4
        @test length(s.beta) == 3 && sort(collect(keys(s.gamma))) == [1, 4]
        # the characters appended to beta are the removed ones, in the order of the indices
        vals = sort([round(Int, 4 * c[a]) for c in s.beta])
        @test vals == [1, 2, 2]
        # a removed character that vanishes on A kills the symbol, vanishing on H alone does not
        cls0 = IndexedClass(G, 5, [1, 2, 3, 4])
        push!(cls0, mk([1, 0, 1, 3]))
        @test iszero(indexed_psi(cls0, [1, 3, 4]))      # c_2 is zero on A and index 2 is removed
        @test iszero(indexed_psi(cls0, [1, 4]))
        cls2 = IndexedClass(G, 5, [1, 2, 3, 4])
        push!(cls2, mk([1, 2, 1, 3]))      # c_2 = ch(2) is trivial on H = <a^2> and nonzero on A
        @test !iszero(indexed_psi(cls2, [1, 3, 4]))
        # J = I is the identity and J = empty gives the unindexed class with H replaced
        @test indexed_psi(cls, [1, 2, 3, 4]) == cls
        @test throws("subset", () -> indexed_psi(cls, [7]))
        # functoriality psi_{J,K} psi_{I,J} = psi_{I,K}
        for (J, K) in (([1, 2, 4], [1, 4]), ([2, 3, 4], [3]), ([1, 2, 3], [2]), ([1, 4], [4]))
            for gs in ([1, 2, 1, 3], [1, 1, 3, 2], [3, 1, 2, 2])
                c0 = IndexedClass(G, 5, [1, 2, 3, 4])
                push!(c0, mk(gs))
                @test indexed_psi(indexed_psi(c0, J), K) == indexed_psi(c0, K)
            end
        end
        # psi and tau do not change d or Y~
        @test s.d == 0 && length(s.Y) == 4
    end

    @testset "class algebra: equal symbols, conjugation and reordering" begin
        G = symmetric_group(4)
        a = perm(G, [2, 1, 3, 4])      # (1 2)
        b = perm(G, [1, 2, 4, 3])      # (3 4)
        x = perm(G, [3, 4, 1, 2])      # (1 3)(2 4) conjugates a to b
        function sy(u, v)
            e1 = indexed_character(G, [u, v], [1, 0])
            e2 = indexed_character(G, [u, v], [0, 1])
            return IndexedSymbol(G, [], [u, v], [u, v], 0, [e1, e2], Dict(0 => indexed_character(G, [u, v], [0, 0])))
        end
        cls = IndexedClass(G, 3, [0])
        push!(cls, sy(a, b))
        @test length(cls) == 1
        # conjugate symbol: swap the roles of the two transpositions, the same symbol by (C) and (O)
        push!(cls, -1, sy(b, a))
        @test iszero(cls)
        # coefficients add and cancel
        push!(cls, 2, sy(a, b)); push!(cls, 3, sy(a, b))
        @test first(values(cls.terms))[1] == 5
        @test (cls - cls) == IndexedClass(G, 3, [0])
        @test 2 * cls == cls + cls
        @test length(cls + (-cls)) == 0
        # conjugation by x sends <a> to <b>, so these two symbols are identified by (C)
        sa = IndexedSymbol(G, [], [a], [a], 0, [indexed_character(G, [a], [1])], Dict(0 => indexed_character(G, [a], [0])))
        sb = IndexedSymbol(G, [], [b], [b], 0, [indexed_character(G, [b], [1])], Dict(0 => indexed_character(G, [b], [0])))
        @test a^x == b
        cj = IndexedClass(G, 2, [0]); push!(cj, sa); push!(cj, -1, sb)
        @test iszero(cj)
        sc = IndexedSymbol(G, [], [a], [a], 0, [indexed_character(G, [a], [1])], Dict(0 => indexed_character(G, [a], [1])))
        cj2 = IndexedClass(G, 2, [0]); push!(cj2, sa); push!(cj2, -1, sc)   # a different gamma is not identified
        @test length(cj2) == 2
        # two genuinely different symbols stay different
        c2 = IndexedSymbol(G, [], [a], [a], 1, [indexed_character(G, [a], [1])], Dict(0 => indexed_character(G, [a], [0])))
        d1 = IndexedClass(G, 3, [0]); push!(d1, c2)
        @test d1 != cls && length(d1 + cls) == 2
    end

    @testset "symbols that differ only in beta, or only in Y~, stay different" begin
        C = cyclic_group(PermGroup, 5)
        g = gen(C, 1)
        c(k) = indexed_character(C, [g], [k])
        mkb(k) = IndexedSymbol(C, [], [g], [g], 0, [c(k)], Dict(0 => c(0)))
        cl = IndexedClass(C, 2, [0])
        push!(cl, mkb(1)); push!(cl, mkb(2))
        @test length(cl) == 2
        # the characters 1 and 4 are inverse, no element of the abelian group C5 conjugates them
        push!(cl, mkb(4))
        @test length(cl) == 3
        # the same A, H, beta, gamma and d with Y~ = A or Y~ = D4 (the group K4 acts) are different symbols
        G = symmetric_group(4)
        s12 = perm(G, [2, 1, 3, 4]); s34 = perm(G, [1, 2, 4, 3]); x = perm(G, [3, 4, 1, 2]); z = s12 * s34
        zero_ = indexed_character(G, [z], [0]); sgn = indexed_character(G, [z], [1])
        ya = IndexedSymbol(G, [z], [z], [z], 1, [], Dict(0 => sgn))
        yd = IndexedSymbol(G, [z], [z], [s12, s34, x], 1, [], Dict(0 => sgn))
        cy = IndexedClass(G, 2, [0]); push!(cy, ya); push!(cy, yd)
        @test length(cy) == 2
    end

    @testset "validation errors" begin
        G = symmetric_group(3)
        t = perm(G, [2, 1, 3]); c3 = cperm(G, [1, 2, 3])
        sg = indexed_character(G, [t], [1])
        z = indexed_character(G, [t], [0])
        gm = Dict(0 => z)
        @test throws("not contained in A", () -> IndexedSymbol(G, [c3], [t], [t], 0, [], gm))
        @test throws("centralizer", () -> IndexedSymbol(G, [], [t], [t, c3], 0, [sg], gm))
        @test throws("abelian", () -> IndexedSymbol(G, [], [t, c3], [t, c3], 0, [], gm))
        @test throws("zero", () -> IndexedSymbol(G, [], [t], [t], 0, [z], gm))
        @test throws("not trivial on H", () -> IndexedSymbol(G, [t], [t], [t], 0, [sg], Dict(0 => sg)))
        @test throws("do not generate the dual of A/H", () -> IndexedSymbol(G, [], [t], [t], 0, [], gm))
        @test throws("do not generate the dual of H", () -> IndexedSymbol(G, [t], [t], [t], 0, [], Dict(0 => z)))
        @test throws("homomorphism", () -> IndexedSymbol(G, [], [t], [t], 0, [Dict(one(G) => 0 // 1, t => 1 // 3)], gm))
        @test throws("not defined on every element", () -> IndexedSymbol(G, [], [t], [t], 0, [Dict(t => 1 // 2)], gm))
        @test throws("nonnegative", () -> IndexedSymbol(G, [], [t], [t], -1, [sg], gm))
        cls = IndexedClass(G, 2, [0])
        ok = IndexedSymbol(G, [], [t], [t], 0, [sg], gm)
        push!(cls, ok)
        @test throws("characters in beta", () -> push!(cls, IndexedSymbol(G, [], [t], [t], 1, [sg], gm)))
        @test throws("index set", () -> push!(cls, IndexedSymbol(G, [], [t], [t], 0, [sg], Dict(1 => z))))
        G4 = symmetric_group(4)
        t4 = perm(G4, [2, 1, 3, 4])
        @test throws("different group", () -> push!(cls, IndexedSymbol(G4, [], [t4], [t4], 0, [indexed_character(G4, [t4], [1])], Dict(0 => indexed_character(G4, [t4], [0])))))
        @test throws("different dimension", () -> cls + IndexedClass(G, 3, [0]))
        @test throws("one exponent", () -> indexed_character(G, [t, c3], [1]))
    end

    @testset "Proposition 9.4 of Kresch-Tschinkel, the chain S3 above S2 (Theorem 8.4)" begin
        G = symmetric_group(4)
        s12 = perm(G, [2, 1, 3, 4]); c123 = cperm(G, [1, 2, 3])
        N, embN = sub(G, [s12, c123])             # S3 = N_{S4}(S3) acting on {1,2,3}
        t, c = gens(N)
        L, embL = sub(N, [t])                     # S2 = N_{S4}(S3 > S2)
        tL = gen(L, 1)
        # printed: [D^o_{S3 > S2} with S2]^naive = (S2 in S2, triv with k, (), (0,0,1)) in Burn_{3,{0,1,2}}(S2, S2)
        zL = indexed_character(L, [tL], [0])
        sL = indexed_character(L, [tL], [1])
        c2 = IndexedClass(L, 3, [0, 1, 2])
        push!(c2, IndexedSymbol(L, [tL], [tL], [tL], 0, [], Dict(0 => zL, 1 => zL, 2 => sL)))
        # the summand of Theorem 8.4: induce after tau and psi with J = {0, 1}, then reindex
        term = indexed_induce(indexed_reindex(indexed_psi(indexed_tau(c2, [0, 1]), [0, 1]), [0, 1]), N, embL)
        zt = indexed_character(N, [t], [0]); st = indexed_character(N, [t], [1])
        zc = indexed_character(N, [c], [0]); sc = indexed_character(N, [c], [1])
        z1 = indexed_character(N, elem_type(N)[], Int[])
        # printed: (triv in S2, triv with k, (1), (0,0))
        printed_sub = IndexedClass(N, 3, [0, 1])
        push!(printed_sub, IndexedSymbol(N, [], [t], [t], 0, [st], Dict(0 => zt, 1 => zt)))
        @test term == printed_sub
        # printed: [D_{S3} with S3] in Burn_{3,{0,1}}(S3, triv), four terms
        T1 = IndexedSymbol(N, [], [], [t, c], 1, [], Dict(0 => z1, 1 => z1))
        T2 = IndexedSymbol(N, [], [t], [t], 0, [st], Dict(0 => zt, 1 => zt))
        T3 = IndexedSymbol(N, [], [t], [t], 0, [st], Dict(0 => zt, 1 => st))
        T4 = IndexedSymbol(N, [], [c], [c], 0, [sc], Dict(0 => zc, 1 => sc))
        D = IndexedClass(N, 3, [0, 1])
        for T in (T1, T2, T3, T4)
            push!(D, T)
        end
        @test length(D) == 4
        naive = D - term                          # [D^o_{S3} with S3]^naive
        expected = IndexedClass(N, 3, [0, 1])
        for T in (T1, T3, T4)
            push!(expected, T)
        end
        # printed: (triv in triv, S3 with k(t), (), (0,0)) + (triv in S2, triv with k, (1), (0,1)) + (triv in C3, triv with k, (1), (0,1))
        @test naive == expected && length(naive) == 3
        @test D != expected
        # sensitivity: the same term built from the conjugate transposition (1 3) is identified with T2 by (C), so it cancels too
        tp = c^-1 * t * c
        @test tp != t
        L2, embL2 = sub(N, [tp])
        tL2 = gen(L2, 1)
        zL2 = indexed_character(L2, [tL2], [0]); sL2 = indexed_character(L2, [tL2], [1])
        c2b = IndexedClass(L2, 3, [0, 1, 2])
        push!(c2b, IndexedSymbol(L2, [tL2], [tL2], [tL2], 0, [], Dict(0 => zL2, 1 => zL2, 2 => sL2)))
        term2 = indexed_induce(indexed_reindex(indexed_psi(indexed_tau(c2b, [0, 1]), [0, 1]), [0, 1]), N, embL2)
        @test D - term2 == expected
        # and a term whose character is wrong (value 0 instead of the sign) does not cancel anything
        wrong = IndexedClass(N, 3, [0, 1])
        push!(wrong, IndexedSymbol(N, [], [c], [c], 0, [sc], Dict(0 => zc, 1 => zc)))
        @test length(D - wrong) == 5
        # psi_{{0,1},{0}} of the naive class gives the two printed lines of the final formula (T1 goes to zero, its c_1 is zero)
        top = indexed_psi(naive, [0])
        want = IndexedClass(N, 3, [0])
        push!(want, IndexedSymbol(N, [], [t], [t], 0, [st, st], Dict(0 => zt)))
        push!(want, IndexedSymbol(N, [], [c], [c], 0, [sc, sc], Dict(0 => zc)))
        @test top == want
        # printed final formula: (triv in S2, triv with k, (1,1), (0)) + (triv in C3, triv with k, (1,1), (0))
        # and inducing to S4 keeps them, as symbols of S4
        up = indexed_induce(top, G, embN)
        want4 = IndexedClass(G, 3, [0])
        e0 = indexed_character(G, [s12], [0])
        push!(want4, IndexedSymbol(G, [], [s12], [s12], 0, [indexed_character(G, [s12], [1]), indexed_character(G, [s12], [1])], Dict(0 => e0)))
        e3 = indexed_character(G, [c123], [0])
        push!(want4, IndexedSymbol(G, [], [c123], [c123], 0, [indexed_character(G, [c123], [1]), indexed_character(G, [c123], [1])], Dict(0 => e3)))
        @test up == want4
        # the wrong character c(1) replaced by c(2) in one place is a different class
        bad = IndexedClass(G, 3, [0])
        push!(bad, IndexedSymbol(G, [], [c123], [c123], 0, [indexed_character(G, [c123], [1]), indexed_character(G, [c123], [2])], Dict(0 => e3)))
        @test bad != IndexedClass(G, 3, [0]) && !(up == bad)
    end

    @testset "Proposition 9.4, the chains S2 wr C2 above C2 and S2 wr C2 (the two lines with K4)" begin
        G = symmetric_group(4)
        s12 = perm(G, [2, 1, 3, 4]); s34 = perm(G, [1, 2, 4, 3]); x = perm(G, [3, 4, 1, 2])
        z = s12 * s34                              # the center of D4, the group diag S2
        zero_ = indexed_character(G, [z], [0]); sgn = indexed_character(G, [z], [1])
        mk(c1, c2) = IndexedSymbol(G, [z], [z], [s12, s34, x], 1, [], Dict(0 => c1, 1 => c2))
        # printed: (diag S2 in diag S2, K4 with k(t), (), (0,1)) for Gamma_1 = S2 wr C2 and (..., (1,1)) for Gamma_1 = C2
        for (c1, c2, wantg) in ((zero_, sgn, zero_), (sgn, sgn, sgn))
            cls = IndexedClass(G, 3, [0, 1]); push!(cls, mk(c1, c2))
            out = indexed_psi(cls, [0])
            # printed: (triv in diag S2, K4 with k(t), (1), (0)) and (triv in diag S2, K4 with k(t), (1), (1))
            want = IndexedClass(G, 3, [0])
            push!(want, IndexedSymbol(G, [], [z], [s12, s34, x], 1, [sgn], Dict(0 => wantg)))
            @test out == want
        end
        # the two outputs are different symbols
        a = IndexedClass(G, 3, [0]); push!(a, IndexedSymbol(G, [], [z], [s12, s34, x], 1, [sgn], Dict(0 => zero_)))
        b = IndexedClass(G, 3, [0]); push!(b, IndexedSymbol(G, [], [z], [s12, s34, x], 1, [sgn], Dict(0 => sgn)))
        @test a != b
    end

    @testset "eta: from the indexed class to BC, with the scalar subgroup trivial and not trivial" begin
        # trivial H: (triv in S2 x S2, triv with k, (e2, e1 + e2), (0)) of Proposition 9.4 goes to (S2 x S2, triv, (e2, e1 + e2))
        G = symmetric_group(4)
        a = perm(G, [2, 1, 3, 4]); b = perm(G, [1, 2, 4, 3])
        e(u, v) = indexed_character(G, [a, b], [u, v])
        cls = IndexedClass(G, 3, [0])
        push!(cls, IndexedSymbol(G, [], [a, b], [a, b], 0, [e(0, 1), e(1, 1)], Dict(0 => e(0, 0))))
        out, Q, proj, dropped = indexed_eta(cls, [])
        @test Q === G && dropped == 0 && out.n == 2
        hand = BCClass(G, 2); push!(hand, BCSymbol(G, [a, b], [], [[0, 1], [1, 1]]))
        @test bc_image(out) == bc_image(hand)
        other = BCClass(G, 2); push!(other, BCSymbol(G, [a, b], [], [[0, 1], [1, 0]]))
        @test bc_image(out) != bc_image(other)
        # the generic symbol (A = H) is not part of a BCClass and is counted
        genc = IndexedClass(G, 3, [0])
        push!(genc, IndexedSymbol(G, [], [], [a], 2, [], Dict(0 => indexed_character(G, elem_type(G)[], Int[]))))
        o2, _, _, d2 = indexed_eta(genc, [])
        @test d2 == 1 && iszero(length(o2.terms))
        @test throws("no BC image", () -> indexed_eta(genc, []; drop_generic = false))
        # H = C2 inside C4, central and nontrivial: (H in A = C4, triv, beta = (1/2 on g), gamma = (1/4 on g)) goes to (C4/H, triv, (1))
        C = cyclic_group(PermGroup, 4)
        g = gen(C, 1)
        beta = indexed_character(C, [g], [2])      # trivial on g^2
        gamma = indexed_character(C, [g], [1])     # c(g^2) = 1/2 nonzero on H
        c4 = IndexedClass(C, 2, [0])
        push!(c4, IndexedSymbol(C, [g^2], [g], [g], 0, [beta], Dict(0 => gamma)))
        o3, Q3, p3, d3 = indexed_eta(c4, [g^2])
        @test d3 == 0 && order(Q3) == 2 && o3.n == 1
        hand3 = BCClass(Q3, 1); push!(hand3, BCSymbol(Q3, [p3(g)], [], [[1]]))
        @test bc_image(o3) == bc_image(hand3)
        # the generic symbol of P(V): (C in C, G/C with k(P(V)), (), epsilon) is dropped
        gv = IndexedClass(C, 2, [0])
        push!(gv, IndexedSymbol(C, [g^2], [g^2], [g], 1, [], Dict(0 => indexed_character(C, [g^2], [1]))))
        @test indexed_eta(gv, [g^2])[4] == 1
        # errors: different first subgroup, non central H
        @test throws("different first subgroup", () -> indexed_eta(c4, []))
        S = symmetric_group(3)
        r = cperm(S, [1, 2, 3])
        sr = IndexedClass(S, 2, [0])
        push!(sr, IndexedSymbol(S, [r], [r], [r], 1, [], Dict(0 => indexed_character(S, [r], [1]))))
        @test throws("central", () -> indexed_eta(sr, [r]))
    end

    @testset "reindexing keeps the order, induction moves Y~, eta keeps Y~" begin
        C = cyclic_group(PermGroup, 5)
        g = gen(C, 1)
        c(k) = indexed_character(C, [g], [k])
        cl = IndexedClass(C, 3, [1, 5])
        push!(cl, IndexedSymbol(C, [], [g], [g], 0, [c(1)], Dict(1 => c(1), 5 => c(2))))
        re = indexed_reindex(cl, [0, 1])
        sr = first(values(re.terms))[2]
        @test re.I == [0, 1] && sr.gamma[0][g] == 1 // 5 && sr.gamma[1][g] == 2 // 5
        # induction transports Y~ when it is larger than A
        G = symmetric_group(4)
        a = perm(G, [2, 1, 3, 4]); b = perm(G, [1, 2, 4, 3])
        L, emb = sub(G, [a, b])
        aL, bL = gens(L)
        cl2 = IndexedClass(L, 2, [0])
        push!(cl2, IndexedSymbol(L, [], [aL], [aL, bL], 0, [indexed_character(L, [aL], [1])], Dict(0 => indexed_character(L, [aL], [0]))))
        up = indexed_induce(cl2, G, emb)
        su = first(values(up.terms))[2]
        @test length(su.Y) == 4 && length(su.A) == 2 && Set(su.Y) == Set([one(G), a, b, a * b])
        # eta keeps the group Y~: A = <a>, Y~ = <a, b> (Y = C2) is a different BC symbol than Y~ = A
        mk(ys) = begin
            cc = IndexedClass(G, 2, [0])
            push!(cc, IndexedSymbol(G, [], [a], ys, 0, [indexed_character(G, [a], [1])], Dict(0 => indexed_character(G, [a], [0]))))
            cc
        end
        o_big = indexed_eta(mk([a, b]), [])[1]
        o_small = indexed_eta(mk([a]), [])[1]
        hand = BCClass(G, 1); push!(hand, BCSymbol(G, [a], [b], [[1]]))
        @test bc_image(o_big) == bc_image(hand)
        @test bc_image(o_big) != bc_image(o_small)
    end

    @testset "induction and reindexing" begin
        G = symmetric_group(4)
        t = perm(G, [2, 1, 3, 4])
        L, emb = sub(G, [t])
        tL = gen(L, 1)
        cl = IndexedClass(L, 2, [3])
        push!(cl, IndexedSymbol(L, [], [tL], [tL], 0, [indexed_character(L, [tL], [1])], Dict(3 => indexed_character(L, [tL], [0]))))
        up = indexed_induce(cl, G, emb)
        @test up.G === G || up.G == G
        s = first(values(up.terms))[2]
        @test t in s.A && length(s.A) == 2
        re = indexed_reindex(cl, [0])
        @test re.I == [0] && sort(collect(keys(first(values(re.terms))[2].gamma))) == [0]
        @test throws("different size", () -> indexed_reindex(cl, [0, 1]))
        @test throws("repeated", () -> indexed_reindex(IndexedClass(L, 3, [0, 1]), [2, 2]))
    end
end
end
