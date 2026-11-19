module TestTransport
using Test, Oscar, EquivariantBurnside
const EB = EquivariantBurnside

# True when f() throws an ArgumentError whose message contains the phrase.
function throws(phrase, f)
    try
        f()
    catch e
        return e isa ArgumentError && occursin(phrase, e.msg)
    end
    return false
end

img(cls) = bc_image(cls)
function cls_of(G, n, terms...)
    c = BCClass(G, n)
    foreach(t -> push!(c, t[1], t[2]), terms)
    return c
end
blockdata(x) = sort([(k.hdesc, k.d, k.ydesc, k.ysize, k.orbitsize) for k in bc_blocks(x)])

@testset "T1 isomorphic presentations: invariants of the induced map" begin
    # S3 as a permutation group and as a polycyclic group, D7 as a permutation group and as a polycyclic group
    for (G1, G2, n, build) in [
        (symmetric_group(3), small_group(6, 1), 2,
         G -> begin
             c3 = first(filter(g -> order(g) == 3, collect(G)))
             [(1, BCSymbol(G, [c3], [c3], [[1], [1]]))]
         end),
        (dihedral_group(PermGroup, 14), small_group(14, 1), 3,
         G -> begin
             r7 = first(filter(g -> order(g) == 7, collect(G)))
             [(1, BCSymbol(G, [r7], [r7], [[1], [1], [2]]))]
         end)]
        f = isomorphism(G1, G2)
        c1 = cls_of(G1, n, build(G1)...)
        c2 = bc_transport(c1, f)
        x1, x2 = img(c1), img(c2)
        @test !is_zero(x1)
        @test is_zero(x1) == is_zero(x2)
        @test order(x1) == order(x2)
        @test blockdata(x1) == blockdata(x2)
        # the transported symbols are made of the images of the generators
        for ((_, s), (_, t)) in zip(c1.terms, c2.terms)
            @test t.betas == s.betas && t.ords == s.ords
            @test all(GAP.Globals.Image(GAP.GapObj(f), a) == b for (a, b) in zip(s.hg, t.hg))
        end
        # round trip through the inverse isomorphism
        c3 = bc_transport(c2, inv(f))
        @test img(c3) == x1
        # additivity and the zero element: transporting a difference gives the difference of images
        d1 = c1 - c1
        @test is_zero(img(bc_transport(d1, f)))
        @test img(bc_transport(2 * c1, f)) == 2 * x2
    end
end

@testset "T2 inner automorphisms act trivially, composition is an action" begin
    S4 = symmetric_group(4)
    c3 = cperm(S4, [1, 2, 3])
    V = [cperm(S4, [1, 2], [3, 4]), cperm(S4, [1, 3], [2, 4])]
    cls = cls_of(S4, 2, (1, BCSymbol(S4, [c3], [c3], [[1], [1]])), (1, BCSymbol(S4, [V[1]], [V[2]], [[1]])))
    x = img(cls)
    @test !is_zero(x)
    g = cperm(S4, [1, 2, 3, 4])
    inner = hom(S4, S4, x -> g * x * inv(g))
    @test img(bc_transport(cls, inner)) == x
    # composition of two inner automorphisms equals the automorphism by the product
    h = cperm(S4, [1, 2])
    inner2 = hom(S4, S4, x -> h * x * inv(h))
    inner12 = hom(S4, S4, x -> (h * g) * x * inv(h * g))
    @test img(bc_transport(bc_transport(cls, inner), inner2)) == img(bc_transport(cls, inner12))
    # a nonzero class is moved to a conjugate class and is not changed in order
    @test order(img(bc_transport(cls, inner12))) == order(x)
end

@testset "T3 Out(G) representatives" begin
    @test length(bc_out_automorphisms(symmetric_group(4))) == 1
    @test length(bc_out_automorphisms(symmetric_group(6))) == 2
    @test length(bc_out_automorphisms(dihedral_group(PermGroup, 12))) == 2
    @test length(bc_out_automorphisms(abelian_group(PermGroup, [3, 3]))) == 48
    # raw GAP group
    reps = bc_out_automorphisms(GAP.Globals.SymmetricGroup(6))
    @test length(reps) == 2 && all(m -> GAP.Globals.IsBijective(m), reps)
    # every representative is an automorphism of G
    G = symmetric_group(6)
    for psi in bc_out_automorphisms(G)
        @test is_bijective(psi) && domain(psi) === G && codomain(psi) === G
    end
end

@testset "T4 the exotic automorphism of S6 moves classes and preserves orders" begin
    G = symmetric_group(6)
    c3 = cperm(G, [1, 2, 3])
    d33 = cperm(G, [1, 2, 3], [4, 5, 6])
    a = cls_of(G, 2, (1, BCSymbol(G, [c3], [c3], [[1], [1]])))
    b = cls_of(G, 2, (1, BCSymbol(G, [d33], [d33], [[1], [1]])))
    xa, xb = img(a), img(b)
    @test !is_zero(xa) && !is_zero(xb)
    reps = bc_out_automorphisms(G)
    # one of the two cosets is the exotic one: it sends the class of 3-cycles to the class of products of two 3-cycles
    moved = [psi for psi in reps if img(bc_transport(a, psi)) != xa]
    @test length(moved) == 1
    psi = moved[1]
    @test img(bc_transport(a, psi)) == xb
    @test img(bc_transport(b, psi)) == xa
    @test order(img(bc_transport(a, psi))) == order(xa)
    # applying the exotic automorphism twice is inner
    @test img(bc_transport(bc_transport(a, psi), psi)) == xa
    # the comparison functions
    @test xa != xb
    w = bc_find_automorphism(a, b)
    @test w !== nothing
    @test img(bc_transport(a, w)) == xb
    @test bc_find_automorphism(a, a) !== nothing
    @test bc_find_automorphism(b, a) !== nothing
    # a class that no automorphism sends to another one has no witness and gets one certificate per coset
    e = cls_of(G, 2, (1, BCSymbol(G, [c3], [c3], [[1], [1]])), (1, BCSymbol(G, [d33], [d33], [[1], [1]])))
    @test bc_find_automorphism(e, a) === nothing
    certs = bc_inequivalence_certificates(e, a)
    @test length(certs) == length(reps)
    @test all(verify, certs) && all(verify_with_group, certs)
    # no certificate exists where a witness exists
    @test throws("vanishes", () -> bc_inequivalence_certificates(a, b))
end

@testset "T5 comparison across presentations" begin
    S3 = symmetric_group(3); P = small_group(6, 1)
    f = isomorphism(S3, P)
    c3 = cperm(S3, [1, 2, 3])
    a = cls_of(S3, 2, (1, BCSymbol(S3, [c3], [c3], [[1], [1]])))
    # the same class built directly in P from the images of the generators
    cP = first(filter(g -> order(g) == 3, collect(P)))
    b = cls_of(P, 2, (1, BCSymbol(P, [cP], [cP], [[1], [1]])))
    @test bc_find_automorphism(a, b, f) !== nothing
    zero = BCClass(P, 2)
    certs = bc_inequivalence_certificates(a, zero, f)
    @test all(verify, certs)
    # without phi the groups differ and the call is refused
    @test throws("different groups", () -> bc_find_automorphism(a, b))
end

@testset "T7 characters transform by the inverse of the exponent (hand computation)" begin
    # In C_m = <h>, the automorphism sigma_k: h -> h^k sends the symbol (C_m, 1, (c_1, c_2)) to the symbol
    # whose character on the image generator h^k equals the old character on h. In terms of the generator h
    # the characters become c * k^-1 mod m, because beta'(h) = beta'((h^k)^(k^-1)) = k^-1 beta(h).
    G = cyclic_group(PermGroup, 7)
    h = gen(G, 1)
    mk(k) = hom(G, G, x -> x^k)
    sym(c) = BCSymbol(G, [h], [], [[c[1]], [c[2]]])
    for (k, kinv) in ((2, 4), (3, 5), (4, 2), (5, 3))
        @test mod(k * kinv, 7) == 1
        for c in ([1, 2], [1, 3], [1, 1])
            a = cls_of(G, 2, (1, sym(c)))
            x = img(bc_transport(a, mk(k)))
            @test x == img(cls_of(G, 2, (1, sym([mod(kinv * c[1], 7), mod(kinv * c[2], 7)]))))
        end
    end
    # the exponent is not irrelevant: some pair of classes is separated, so the test above is not vacuous
    a = cls_of(G, 2, (1, sym([1, 2])))
    @test !is_zero(img(a))
    @test img(bc_transport(a, mk(2))) != img(cls_of(G, 2, (1, sym([2, 4]))))
end

@testset "T8 the Y part is transported (C_9, H = <g^3>, Y = C_9)" begin
    G = cyclic_group(PermGroup, 9)
    g = gen(G, 1); h = g^3
    withY(c) = cls_of(G, 2, (1, BCSymbol(G, [h], [g], [[c], [c]])))
    noY(c) = cls_of(G, 2, (1, BCSymbol(G, [h], [], [[c], [c]])))
    # Y is visible: both images are nonzero and different, so a transport that forgets Y is detected
    @test !is_zero(img(withY(1))) && !is_zero(img(noY(1))) && img(withY(1)) != img(noY(1))
    for k in (2, 4, 5, 7, 8)
        sigma = hom(G, G, x -> x^k)
        # sigma sends h = g^3 to h^k, so the character c of H becomes c * k^-1 mod 3 in terms of h
        kinv = mod(invmod(k, 3), 3)
        @test img(bc_transport(withY(1), sigma)) == img(withY(mod(kinv, 3)))
        @test img(bc_transport(withY(2), sigma)) == img(withY(mod(2 * kinv, 3)))
        @test img(bc_transport(withY(1), sigma)) != img(noY(mod(kinv, 3)))
    end
end

@testset "T6 errors" begin
    S3 = symmetric_group(3); S4 = symmetric_group(4)
    c3 = cperm(S3, [1, 2, 3])
    s = BCSymbol(S3, [c3], [c3], [[1], [1]])
    # a homomorphism defined on another group
    id4 = hom(S4, S4, x -> x)
    @test throws("not defined on the group", () -> bc_transport(s, id4))
    @test throws("not defined on the group", () -> bc_transport(BCClass(S3, 2), id4))
    # a homomorphism that is not injective
    C2 = cyclic_group(PermGroup, 2)
    f = hom(S3, C2, x -> sign(x) == 1 ? one(C2) : gen(C2, 1))
    @test throws("not an isomorphism", () -> bc_transport(s, f))
    # the classes have different n
    a = cls_of(S3, 2, (1, s)); b = cls_of(S3, 3, (1, s))
    @test throws("different n", () -> bc_find_automorphism(a, b))
end

end
