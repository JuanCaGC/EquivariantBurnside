module TestFieldAdversarial
include("g1_adversarial_helpers.jl")

@testset "Independent projective eigenvalue ratios" begin
    M = matrix_group("DiagonalMat([1,E(5),E(5)^2])")
    expected = sort([1//5, 1//5, 2//5, 3//5, 4//5, 4//5])
    @test projective_invariant(M) == expected
    @test projective_invariant(GG.E(7) * M) == expected
    T = matrix_group("[[1,1,0],[0,1,1],[0,0,1]]")
    @test projective_invariant(inv(T) * M * T) == expected
    @test projective_invariant(matrix_group("DiagonalMat([1,E(5),E(5)^3])")) != expected
    @test projective_invariant(matrix_group("IdentityMat(3)")) == fill(0//1, 6)
    @test_throws ArgumentError set_field_key_mode!(:invalid)
end

@testset "Independent fixed point signatures" begin
    for (name, code) in (("C5", C5_CODE), ("S3", S3_CODE), ("A4", A4_CODE),
                         ("S4", S4_CODE), ("Heisenberg27", HEIS_CODE),
                         ("Q8", Q8_CODE), ("Dic16", DIC16_CODE))
        @testset "$name" begin
            rep = linrep(matrix_group(code))
            cls = projective_class(rep, fields=true)
            @test first(field_faithful(cls))
            generic = only([s for (c,s) in values(cls.terms) if s.d == rep.n - 1])
            sig = field_fixed_signature(generic)
            @test !isempty(sig)
            for (B, fixed) in sig
                # In these scalar central extensions noncommuting lifts obstruct a line.
                expected = name in ("Heisenberg27", "Q8", "Dic16") ?
                    all(x*y == y*x for x in B for y in B) : true
                @test fixed == expected
            end
            if name == "Heisenberg27"
                @test count(identity, values(sig)) == 5
                @test count(!, values(sig)) == 1
            elseif name == "Q8"
                @test count(identity, values(sig)) == 4
                @test count(!, values(sig)) == 1
            end
            @test compare_fields(cls, generic, deepcopy(generic)) == :equal
            @test field_pair_report(cls).equal == 0
            @test !isempty(field_fingerprint(cls))
        end
    end
end
# Independent constructors for controlled field comparisons.
function factor_from_matrices(mats)
    dims = unique(Int(GG.Length(m)) for m in values(mats))
    dim = only(dims)
    FieldFactor(dim,
        Dict(g => projective_invariant(m) for (g,m) in mats),
        Dict(g => GG.TraceMat(m) for (g,m) in mats),
        Dict(g => m for (g,m) in mats))
end
function replace_field(s, F)
    IndexedSymbol(s.G, s.H, s.A, s.Y, s.d, s.beta, s.gamma, field=F)
end
function generic_symbol(cls, d)
    only([s for (c,s) in values(cls.terms) if s.d == d])
end
function generic_class(cls, d)
    s = generic_symbol(cls, d)
    result = IndexedClass(cls.G, cls.n, cls.I)
    push!(result, s)
    result
end

@testset "Field transformations and missing data" begin
    rep = linrep(scalar_extension(matrix_group(S4_CODE), 5))
    cls = plus_divisor_symbols(rep)
    s = first(values(cls.terms))[2]
    T = matrix_group("[[1,1,0],[0,1,1],[0,0,1]]")
    changed = factor_from_matrices(Dict(g => inv(T)*m*T for (g,m) in rep.mats))
    t = replace_field(s, [changed])
    @test compare_fields(cls, s, t) == :equal
    @test field_fixed_signature(t) == field_fixed_signature(s)
    scalar_changed = factor_from_matrices(Dict(g => GG.E(7)*m for (g,m) in rep.mats))
    u = replace_field(s, [scalar_changed])
    @test field_fixed_signature(u) == field_fixed_signature(s)
    determinant_twist = factor_from_matrices(Dict(g => GG.DeterminantMat(m)*m for (g,m) in rep.mats))
    v = replace_field(s, [determinant_twist])
    @test compare_fields(cls, s, v) == :equal
    # Each lift can be multiplied by a root of unity for fixed point tests.
    missing = IndexedSymbol(s.G, s.H, s.A, s.Y, s.d, s.beta, s.gamma)
    @test_throws ArgumentError field_fixed_signature(missing)
    @test_throws ArgumentError certify_incompressible_dim3(missing)
    lost = replace_field(s, [FieldFactor(f.dim, f.inv) for f in s.F])
    @test_throws ArgumentError field_fixed_signature(lost)
    trivial = factor_from_matrices(Dict(g => GG.IdentityMat(3) for g in rep.els))
    bad = replace_field(s, [trivial])
    @test_throws ArgumentError certify_incompressible_dim3(bad)
    badclass = IndexedClass(cls.G, cls.n, cls.I)
    push!(badclass, bad)
    @test !first(field_faithful(badclass))
end

@testset "Product retains lifts and sees its second factor" begin
    trivial_rep = linrep(matrix_group("Group(IdentityMat(2))"))
    qrep = linrep(matrix_group(Q8_CODE))
    c1 = projective_class(trivial_rep, fields=true)
    c2 = projective_class(qrep, fields=true)
    c1 = generic_class(c1, 1)
    c2 = generic_class(c2, 1)
    c2 = indexed_reindex(c2, [1])
    product, P, emb1, emb2 = indexed_product(c1,c2)
    s = only(values(product.terms))[2]
    @test length(s.F) == 2
    @test all(!isempty(f.mat) for f in s.F)
    @test first(field_faithful(product))
    sig = field_fixed_signature(s)
    @test count(identity, values(sig)) == 4
    @test count(!, values(sig)) == 1
    @test sig[Set(s.Y)] == false
end

@testset "Two A5 plane representations are not separated by fixed points" begin
    rep = linrep(irreducible_three("AlternatingGroup(5)"))
    cls = projective_class(rep, fields=true)
    s = generic_symbol(cls, 2)
    # The two degree three characters are exchanged by sqrt(5) -> -sqrt(5).
    gal = matrix_group("m -> List(m, row -> List(row, x -> GaloisCyc(x,2)))")
    mats = Dict(g => gal(m) for (g,m) in rep.mats)
    t = replace_field(s, [factor_from_matrices(mats)])
    @test any(GG.TraceMat(rep.mats[g]) != GG.TraceMat(mats[g]) for g in rep.els)
    @test all(values(field_fixed_signature(s)))
    @test all(values(field_fixed_signature(t)))
    @test compare_fields(cls, s, t) == :unknown
end

@testset "Gamma is part of the conjugacy data" begin
    rep = linrep(scalar_extension(matrix_group(S3_CODE), 5))
    cls = projective_class(rep, fields=true)
    s = generic_symbol(cls, 2)
    gam = Dict(i => Dict(g => mod(2*v,1) for (g,v) in chi) for (i,chi) in s.gamma)
    t = IndexedSymbol(s.G, s.H, s.A, s.Y, s.d, s.beta, gam, field=s.F)
    @test_throws ArgumentError compare_fields(cls, s, t)
    doubled = IndexedClass(cls.G, cls.n, cls.I)
    push!(doubled, s)
    push!(doubled, t)
    @test length(doubled) == 2
    @test field_pair_report(doubled).pairs == 0
end

@testset "Noncentral conjugation transports the second field" begin
    rep = linrep(matrix_group(S4_CODE))
    G = rep.P
    a = first(x for x in rep.els if order(x) == 3)
    Y = [one(G), a, a^2]
    h = first(x for x in rep.els if Set(inv(x)*y*x for y in Y) != Set(Y))
    z = GG.E(3)
    mats = Dict(a^i => GG.DiagonalMat(Oscar.GAP.GapObj([1,1,z^i])) for i in 0:2)
    F = factor_from_matrices(mats)
    chi0 = Dict(one(G) => 0//1)
    s = IndexedSymbol(G, [], [], Y, 2, [], Dict(0 => chi0), field=[F])
    transported = Dict(inv(h)*y*h => m for (y,m) in mats)
    t = IndexedSymbol(G, [], [], collect(keys(transported)), 2, [], Dict(0 => chi0),
        field=[factor_from_matrices(transported)])
    cls = IndexedClass(G, 3, [0])
    @test compare_fields(cls, s, t) == :equal
end

@testset "Klein obstruction separates plane and ruled fields" begin
    # Binary octahedral matrices, with quotient S4 and scalar kernel of order two.
    binary = matrix_group("Group(DiagonalMat([E(8),E(8)^-1]),[[0,1],[-1,0]],[[1+E(4),1+E(4)],[-1+E(4),1-E(4)]]/2)")
    @test sizegroup(binary) == 48
    rep = linrep(binary)
    sym2 = matrix_group("m -> [[m[1][1]^2,m[1][1]*m[1][2],m[1][2]^2],[2*m[1][1]*m[2][1],m[1][1]*m[2][2]+m[1][2]*m[2][1],2*m[1][2]*m[2][2]],[m[2][1]^2,m[2][1]*m[2][2],m[2][2]^2]]")
    plane = factor_from_matrices(Dict(g => sym2(m) for (g,m) in rep.mats))
    line = factor_from_matrices(rep.mats)
    trivial = factor_from_matrices(Dict(g => GG.IdentityMat(2) for g in rep.els))
    c = only([g for g in rep.C if g != one(rep.P)])
    epsilon = indexed_character(rep.P, [c], [1])
    s = IndexedSymbol(rep.P, [], rep.C, rep.els, 2, [epsilon], Dict(), field=[plane])
    t = replace_field(s, [line, trivial])
    cls = IndexedClass(rep.P, 3, [])
    @test compare_fields(cls, s, t) == :different
    @test all(values(field_fixed_signature(s)))
    @test any(!, values(field_fixed_signature(t)))
    @test certify_incompressible_dim3(s).certified
    @test !certify_incompressible_dim3(t).certified
    push!(cls,s)
    push!(cls,t)
    @test field_pair_report(cls) == (classes=1, pairs=1, equal=0, different=1, unknown=0)
end

@testset "Generic fingerprint derived from a diagonal C5 action" begin
    rep = linrep(matrix_group(C5_CODE))
    cls = generic_class(projective_class(rep, fields=true), 2)
    key, coefficient = only(field_fingerprint(cls))
    @test coefficient == 1
    @test key[1:4] == (1,1,5,2)
    @test collect(key[5]) == [0]
    @test isempty(key[6])
    @test collect(key[7]) == [(0,1)]
    @test collect(key[8]) == [(3,5,1)]
    s = only(values(cls.terms))[2]
    @test_throws ArgumentError certify_incompressible_dim3(s)
    T = matrix_group("[[1,1,0],[0,1,1],[0,0,1]]")
    conjugated = GG.Group(Oscar.GAP.GapObj([inv(T)*g*T for g in elements(rep.G)]))
    changed = generic_class(projective_class(linrep(conjugated), fields=true), 2)
    @test field_fingerprint(changed) == field_fingerprint(cls)
end

@testset "Lift matrices survive products, restrictions and moves of the recursion" begin
    # Block diagonal and monomial groups in dimension 3 go through the vector product, the restriction and the move of fields.
    # Every symbol with a field datum must keep its lift matrices, so its fixed point signature exists. The signature is
    # monotone (a subgroup of a group with a fixed point has one) and holds on A itself, because A acts by scalars on every factor.
    cyc = "[[0,1,0],[0,0,1],[1,0,0]]"
    swp = "[[0,1,0],[1,0,0],[0,0,1]]"
    dg(n, a, b, c) = "[[E($n)^$a,0,0],[0,E($n)^$b,0],[0,0,E($n)^$c]]"
    codes = ["Group(" * dg(2, 1, 1, 0) * "," * dg(2, 0, 1, 1) * "," * cyc * ")",
             "Group(" * dg(2, 1, 1, 0) * "," * dg(2, 0, 1, 1) * "," * cyc * "," * swp * ")",
             "Group(" * dg(3, 1, 1, 1) * "," * dg(4, 1, 0, 0) * ")"]
    for code in codes
        rep = linrep(matrix_group(code))
        cls = projective_class(rep, fields=true)
        for (_, (_, s)) in cls.terms
            isempty(s.F) && continue
            @test all(!isempty(f.mat) for f in s.F)
            sig = field_fixed_signature(s)
            @test get(sig, Set{Any}(s.A), false)
            for (B, v) in sig, (B2, v2) in sig
                if v && issubset(B2, B)
                    @test v2
                end
            end
        end
    end
end
end
