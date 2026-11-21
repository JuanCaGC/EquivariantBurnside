module TestIndexedOps
using Test, Oscar, EquivariantBurnside, LinearAlgebra

function throws(phrase, f)
    try
        f()
    catch e
        return e isa ArgumentError && occursin(phrase, e.msg)
    end
    return false
end

# the first stored symbol of a class
firstsym(cls) = first(values(cls.terms))[2]

@testset "indexed omega, restriction and product" begin
    @testset "omega: Definition on a cyclic group of order 12" begin
        G = cyclic_group(PermGroup, 12)
        g = gen(G, 1)
        ch(k) = indexed_character(G, [g], [k])       # the character g -> k/12
        mk(gs) = IndexedSymbol(G, [g^6], [g], [g], 0, [ch(2)], Dict(i => ch(k) for (i, k) in enumerate(gs)))
        function cl(gs)
            c = IndexedClass(G, 1 + length(gs), collect(1:length(gs)))
            push!(c, mk(gs))
            return c
        end
        # I = {1,2,3}, remove index 2 with the character of order 3: A' = <g^3> of order 4, H cap A' = <g^6>
        out = indexed_omega(cl([1, 4, 3]), [1, 3])
        s = firstsym(out)
        @test out.I == [1, 3] && out.n == 4
        @test length(s.A) == 4 && length(s.H) == 2 && s.d == 1 && length(s.beta) == 1
        @test length(s.Y) == 12                     # Y~ is NOT shrunk, the centralizer is that of the original A
        @test sort(collect(keys(s.gamma))) == [1, 3]
        # the restriction of beta = ch(2) to <g^3> sends g^3 to 6/12
        @test s.beta[1][g^3] == 1 // 2
        # the removed character of order 4 on A has kernel of order 3: H' = trivial, A' = <g^4> of order 3
        out2 = indexed_omega(cl([1, 3, 3]), [1, 3])
        s2 = firstsym(out2)
        @test length(s2.A) == 3 && length(s2.H) == 1 && s2.d == 1
        # a removed character with kernel exactly H kills the symbol because beta restricts to zero
        @test iszero(indexed_omega(cl([1, 2, 3]), [1, 3]))
        # a removed zero character is allowed, nothing is restricted and d goes up
        out3 = indexed_omega(cl([1, 0, 3]), [1, 3])
        s3 = firstsym(out3)
        @test length(s3.A) == 12 && length(s3.H) == 2 && s3.d == 1
        # J = I is the identity, J = empty needs H cap the kernels trivial and raises d by |I|
        @test indexed_omega(cl([1, 4, 3]), [1, 2, 3]) == cl([1, 4, 3])
        out4 = indexed_omega(cl([3, 3, 3]), Int[])
        @test out4.I == Int[] && !iszero(out4) && firstsym(out4).d == 3
        @test throws("subset", () -> indexed_omega(cl([1, 4, 3]), [9]))
        @test throws("repeated", () -> indexed_omega(cl([1, 4, 3]), [1, 1]))
    end

    @testset "identities of Lemma 4.6: functoriality and the exchange of omega and psi" begin
        G = cyclic_group(PermGroup, 12)
        g = gen(G, 1)
        ch(k) = indexed_character(G, [g], [k])
        mk(gs) = IndexedSymbol(G, [g^6], [g], [g], 0, [ch(2)], Dict(i => ch(k) for (i, k) in enumerate(gs)))
        function cl(gs)
            c = IndexedClass(G, 1 + length(gs), collect(1:length(gs)))
            push!(c, mk(gs))
            return c
        end
        gsets = ([1, 4, 3, 6], [1, 0, 3, 4], [3, 1, 4, 5], [1, 2, 3, 8], [5, 6, 3, 9], [1, 3, 3, 3], [7, 0, 0, 1])
        nz = 0
        for gs in gsets
            c0 = cl(gs)
            for (J, K) in (([1, 2, 4], [1, 4]), ([2, 3, 4], [3]), ([1, 2, 3], [2]), ([1, 4], [4]), ([1, 2, 3, 4], Int[]))
                # omega_{J,K} omega_{I,J} = omega_{I,K}
                l = indexed_omega(indexed_omega(c0, J), K)
                r = indexed_omega(c0, K)
                @test l == r
                nz += !iszero(r)
                # omega_{J,K} psi_{I,J} = psi_{(I minus J) cup K, K} omega_{I,(I minus J) cup K}
                IJ = [i for i in c0.I if !(i in J)]
                M = sort(union(IJ, K))
                lhs = indexed_omega(indexed_psi(c0, J), K)
                rhs = indexed_psi(indexed_omega(c0, M), K)
                @test lhs == rhs
                nz += !iszero(rhs)
            end
        end
        @test nz >= 10                  # the identities are not only checked on zero classes
    end

    @testset "restriction: Example 7.1 of KT-struct (D4 and C4)" begin
        S4 = symmetric_group(4)
        D4, _ = sub(S4, [perm(S4, [2, 3, 4, 1]), perm(S4, [3, 2, 1, 4])])
        r = D4(perm(S4, [2, 3, 4, 1]))
        chi = indexed_character(D4, [r], [1])
        cls = IndexedClass(D4, 1, Int[])
        push!(cls, IndexedSymbol(D4, [], [r], [r], 0, [chi], Dict{Int,Dict{Any,Rational{Int}}}()))
        out, L, emb = indexed_restrict(cls, [r])
        @test order(L) == 4 && length(out) == 2
        # the two terms are the characters 1 and 3 of C4 (the printed answer of Example 7.1)
        gL = preimage(emb, r)
        gLv(s) = s.beta[1][gL]
        @test sort([gLv(s) for (_, (c, s)) in out.terms]) == [1 // 4, 3 // 4]
        @test all(c == 1 for (_, (c, s)) in out.terms)
        # coefficients are carried through: a class with coefficient 3 restricts to terms with coefficient 3
        cls3 = IndexedClass(D4, 1, Int[])
        push!(cls3, 3, IndexedSymbol(D4, [], [r], [r], 0, [chi], Dict{Int,Dict{Any,Rational{Int}}}()))
        out3, _, _ = indexed_restrict(cls3, [r])
        @test length(out3) == 2 && all(c == 3 for (_, (c, s)) in out3.terms)
        # restriction to D4 itself is the identity on the class and restriction to the trivial group kills a beta symbol
        outG, LG, _ = indexed_restrict(cls, [one(D4)] ∪ [g for g in gens(D4)])
        @test length(outG) == 1 && order(LG) == 8
        outT, LT, _ = indexed_restrict(cls, [one(D4)])
        @test order(LT) == 1 && iszero(outT)
    end

    @testset "restriction: brute force weighted sum over all group elements agrees with the double cosets" begin
        G = symmetric_group(4)
        a = perm(G, [2, 1, 3, 4])   # (1 2)
        b = perm(G, [1, 2, 4, 3])   # (3 4)
        c3 = perm(G, [2, 3, 1, 4])
        function sy1(u)             # (triv in <u>, <u>, (1))
            return IndexedSymbol(G, [], [u], [u], 0, [indexed_character(G, [u], [1])], Dict{Int,Dict{Any,Rational{Int}}}())
        end
        s_a = sy1(a)
        s_c3 = sy1(c3)
        e1 = indexed_character(G, [a, b], [1, 0])
        e2 = indexed_character(G, [a, b], [0, 1])
        s_ab = IndexedSymbol(G, [], [a, b], [a, b], 0, [e1, e2], Dict{Int,Dict{Any,Rational{Int}}}())
        s_big = IndexedSymbol(G, [], [a], [a, b], 0, [indexed_character(G, [a], [1])], Dict{Int,Dict{Any,Rational{Int}}}())
        s_ind = IndexedSymbol(G, [], [a], [a, b], 0, [indexed_character(G, [a], [1])], Dict(0 => indexed_character(G, [a], [1])))
        Ls = (
            [perm(G, [2, 3, 1, 4]), perm(G, [2, 1, 3, 4])],            # S3
            [perm(G, [2, 3, 4, 1]), perm(G, [3, 2, 1, 4])],            # D4
            [perm(G, [2, 1, 3, 4]), perm(G, [3, 4, 1, 2])],            # a group of order 4
            [perm(G, [2, 1, 3, 4])],                                    # C2
            [perm(G, [2, 1, 4, 3]), perm(G, [3, 4, 1, 2])],            # Klein four group
            [perm(G, [2, 3, 1, 4]), perm(G, [2, 1, 4, 3])],            # A4
        )
        nonzero = 0
        for (s, I, n) in ((s_a, Int[], 1), (s_c3, Int[], 1), (s_ab, Int[], 2), (s_big, Int[], 1), (s_ind, [0], 2))
            cls = IndexedClass(G, n, I)
            push!(cls, s)
            for Lg in Ls
                out, L, emb = indexed_restrict(cls, Lg)
                Lset = Dict{Any,Any}(emb(l) => l for l in L)
                # brute force: sum over all k in G of |L cap k Y k^-1| times the term at g = k^-1, divided by |L||Y|
                bf = IndexedClass(L, n, I)
                for k in G
                    g = inv(k)
                    keep(x) = haskey(Lset, x^g)
                    w = count(y -> haskey(Lset, k * y * inv(k)), s.Y)
                    beta2 = [Dict{Any,Rational{Int}}(Lset[x^g] => v for (x, v) in cc if keep(x)) for cc in s.beta]
                    any(all(iszero(v) for v in values(cc)) for cc in beta2) && continue
                    A2 = Any[Lset[x^g] for x in s.A if keep(x)]
                    H2 = Any[Lset[x^g] for x in s.H if keep(x)]
                    Y2 = Any[Lset[x^g] for x in s.Y if keep(x)]
                    gm = Dict{Int,Dict{Any,Rational{Int}}}(i => Dict{Any,Rational{Int}}(Lset[x^g] => v for (x, v) in cc if keep(x)) for (i, cc) in s.gamma)
                    push!(bf, w, IndexedSymbol(L, H2, A2, Y2, s.d, beta2, gm))
                end
                @test bf == (Int(order(L)) * length(s.Y)) * out
                nonzero += !iszero(out)
            end
        end
        @test nonzero >= 12
    end

    @testset "restriction: transitivity and commutation with psi and omega" begin
        G = symmetric_group(4)
        a = perm(G, [2, 1, 3, 4])
        b = perm(G, [1, 2, 4, 3])
        e1 = indexed_character(G, [a, b], [1, 0])
        e2 = indexed_character(G, [a, b], [0, 1])
        e3 = indexed_character(G, [a, b], [1, 1])
        z = indexed_character(G, [a, b], [0, 0])
        cls = IndexedClass(G, 3, [0, 1])
        push!(cls, IndexedSymbol(G, [b], [a, b], [a, b], 0, [e1], Dict(0 => e2, 1 => e3)))
        push!(cls, IndexedSymbol(G, [], [a], [a, b], 0, [indexed_character(G, [a], [1])], Dict(0 => indexed_character(G, [a], [1]), 1 => indexed_character(G, [a], [0]))))
        # transitivity of restriction: S4 to D4 to its subgroup K, same as S4 directly to K
        Dg = [perm(G, [2, 3, 4, 1]), perm(G, [3, 2, 1, 4])]
        K4 = [perm(G, [2, 1, 4, 3]), perm(G, [3, 4, 1, 2])]
        r1, L1, e1m = indexed_restrict(cls, Dg)
        Kin = [preimage(e1m, k) for k in K4]
        r2, L2, e2m = indexed_restrict(r1, Kin)
        r3, L3, _ = indexed_restrict(cls, K4)
        @test order(L2) == 4 && order(L3) == 4
        @test length(r2) == length(r3) && length(r3) > 0 && length(r1) > 0
        # the two classes live in different group objects, compare through the stored sizes of the symbols and the coefficients
        sig(c) = sort([(coef, length(s.H), length(s.A), length(s.Y), length(s.beta)) for (_, (coef, s)) in c.terms])
        @test sig(r2) == sig(r3)
        # restriction commutes with psi and with omega (same group object L inside one restriction)
        for J in ([0], [1], Int[])
            outA, LA, _ = indexed_restrict(indexed_psi(cls, J), Dg)
            rr, _, _ = indexed_restrict(cls, Dg)
            @test outA == indexed_psi(rr, J)
            J == [0] && @test !iszero(outA)
            outB, LB, _ = indexed_restrict(indexed_omega(cls, J), Dg)
            @test outB == indexed_omega(rr, J)
            J == [1] && @test !iszero(outB)
        end
    end

    @testset "product: formula (6.1) in subgroup notation" begin
        C = cyclic_group(PermGroup, 2)
        t = gen(C, 1)
        chi = indexed_character(C, [t], [1])
        z = Dict(one(C) => 0 // 1, t => 0 // 1)
        a = IndexedClass(C, 1, Int[])
        push!(a, IndexedSymbol(C, [], [t], [t], 0, [chi], Dict{Int,Dict{Any,Rational{Int}}}()))
        out, P, e1, e2 = indexed_product(a, a)
        s = firstsym(out)
        @test order(P) == 4 && out.n == 2 && length(out) == 1
        @test length(s.A) == 4 && length(s.H) == 1 && length(s.Y) == 4 && s.d == 0 && length(s.beta) == 2
        x1, x2 = e1(t), e2(t)
        vals = sort([sort([c[x1], c[x2]]) for c in s.beta])
        @test vals == [[0 // 1, 1 // 2], [0 // 1, 1 // 2]]
        @test s.beta[1][x1 * x2] == 1 // 2 && s.beta[2][x1 * x2] == 1 // 2
        # d adds and the product of classes with several terms multiplies the coefficients
        b = IndexedClass(C, 1, Int[])
        push!(b, 3, IndexedSymbol(C, [], [t], [t], 0, [chi], Dict{Int,Dict{Any,Rational{Int}}}()))
        out2, _, _, _ = indexed_product(a, b)
        @test only(values(out2.terms))[1] == 3
        # d adds, and Y~ larger than A is kept as the product of the Y~ (not shrunk to the product of the A)
        S4 = symmetric_group(4)
        u = perm(S4, [2, 1, 3, 4])
        v = perm(S4, [1, 2, 4, 3])
        chu = indexed_character(S4, [u], [1])
        sb = IndexedSymbol(S4, [], [u], [u, v], 1, [chu], Dict{Int,Dict{Any,Rational{Int}}}())
        cb = IndexedClass(S4, 2, Int[])
        push!(cb, sb)
        outb, _, _, _ = indexed_product(cb, cb)
        sbb = firstsym(outb)
        @test outb.n == 4 && sbb.d == 2 && length(sbb.beta) == 2
        @test length(sbb.A) == 4 && length(sbb.Y) == 16
        # indexed classes with disjoint index sets
        ai = IndexedClass(C, 2, [0])
        push!(ai, IndexedSymbol(C, [], [t], [t], 0, [chi], Dict(0 => chi)))
        bi = IndexedClass(C, 2, [1])
        push!(bi, IndexedSymbol(C, [], [t], [t], 0, [chi], Dict(1 => chi)))
        outi, Pi, _, _ = indexed_product(ai, bi)
        @test outi.I == [0, 1] && outi.n == 4 && length(firstsym(outi).beta) == 2
        @test throws("disjoint", () -> indexed_product(ai, ai))
        # psi commutes with the product: psi_{I1 u I2, J1 u J2}(a * b) = psi(a) * psi(b)
        l = indexed_psi(outi, [0])
        ra, _, _, _ = indexed_product(indexed_psi(ai, [0]), indexed_psi(bi, Int[]))
        @test l == ra
        l2 = indexed_omega(outi, [1])
        ra2, _, _, _ = indexed_product(indexed_omega(ai, Int[]), indexed_omega(bi, [1]))
        @test l2 == ra2
        # a trivial class has no symbols and the product with it is zero
        @test iszero(indexed_product(a, IndexedClass(C, 0, Int[]))[1])
    end
end
end
