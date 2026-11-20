module TestTransportAdversarial
using Test, Oscar, EquivariantBurnside
const B = EquivariantBurnside
function cls(G,h,w,n=2)
    c = BCClass(G,n)
    push!(c,BCSymbol(G,[h],[],[[a] for a in w]))
    c
end

@testset "Outer automorphisms from elementary group theory" begin
    for (G,expected) in [(cyclic_group(7),6), (dihedral_group(12),2),
                         (small_group(9,2),48), (small_group(8,4),6),
                         (symmetric_group(6),2)]
        @test length(bc_out_automorphisms(G)) == expected
    end
    G = symmetric_group(6)
    a = cperm(G,[1,2,3])
    double = cperm(G,[1,2,3],[4,5,6])
    reps = bc_out_automorphisms(G)
    cycle_counts(x) = sort([length(c) for c in GAP.gap_to_julia(GAP.Globals.Cycles(gapobj(x),GAP.GapObj(collect(1:6))))])
    @test Set(Tuple(cycle_counts(f(a))) for f in reps) == Set([(1,1,1,3),(3,3)])
    @test Set(Tuple(cycle_counts(f(double))) for f in reps) == Set([(1,1,1,3),(3,3)])
end

@testset "Characters follow the inverse exponent" begin
    G = cyclic_group(PermGroup,7)
    h = first(gens(G))
    c = cls(G,h,[1,2])
    for k in 1:6
        f = hom(G,G,[h],[h^k])
        inverse = invmod(k,7)
        expected = cls(G,h,mod.([inverse,2inverse],7))
        @test bc_image(bc_transport(c,f)) == bc_image(expected)
        back = hom(G,G,[h],[h^inverse])
        @test bc_image(bc_transport(bc_transport(c,f),back)) == bc_image(c)
        for j in 1:6
            g = hom(G,G,[h],[h^j])
            composite = hom(G,G,[h],[h^mod(j*k,7)])
            @test bc_image(bc_transport(bc_transport(c,f),g)) == bc_image(bc_transport(c,composite))
        end
        @test bc_image(bc_transport(3*c,f)) == 3*bc_image(expected)
    end
    bad = hom(G,G,[h],[one(G)])
    @test_throws ArgumentError bc_transport(c,bad)
    H = cyclic_group(5)
    @test_throws ArgumentError bc_transport(c,hom(H,H,gens(H),gens(H)))
    # In dimension one distinct nonzero cyclic characters are free generators.
    free = cls(G,h,[1],1)
    @test order(bc_image(free)) === nothing
    f = hom(G,G,[h],[h^2])
    @test bc_image(bc_transport(free,f)) == bc_image(cls(G,h,[4],1))
    @test bc_image(bc_transport(free,f)) != bc_image(cls(G,h,[2],1))
    @test bc_image(free) != -bc_image(free)
    zero = BCClass(G,1)
    certs = bc_inequivalence_certificates(free,zero)
    @test length(certs) == 6
    @test all(verify,certs)
    @test all(verify_with_group,certs)
    @test bc_find_automorphism(free,zero) === nothing
    @test bc_find_automorphism(free,bc_transport(free,f)) !== nothing
    @test_throws ArgumentError bc_inequivalence_certificates(free,bc_transport(free,f))
end

@testset "Inner automorphisms and a different group realization" begin
    G = symmetric_group(3)
    h = cperm(G,[1,2,3])
    c = cls(G,h,[1,1])
    for a in collect(G)
        phi = hom(G,G,gens(G),[a*g*inv(a) for g in gens(G)])
        @test bc_image(bc_transport(c,phi)) == bc_image(c)
    end
    H = small_group(6,1)
    f = isomorphism(G,H)
    @test order(bc_image(bc_transport(c,f))) == 2
    @test bc_image(bc_transport(bc_transport(c,f),inv(f))) == bc_image(c)
end
@testset "Two independent character directions" begin
    G = GAP.Globals.AbelianGroup(GAP.Globals.IsPermGroup,GAP.GapObj([3,3]))
    generators = GAP.Globals.GeneratorsOfGroup(G)
    h,k = generators[1],generators[2]
    phi = GAP.Globals.GroupHomomorphismByImages(G,G,generators,GAP.GapObj([h*k,k]))
    s = BCSymbol(G,[h,k],[],[[1,0],[0,1]])
    expected = BCSymbol(G,[h,k],[],[[1,0],[-1,1]])
    @test bc_image(bc_transport(s,phi),2) == bc_image(expected,2)
    @test bc_image(bc_transport(bc_transport(bc_transport(s,phi),phi),phi),2) == bc_image(s,2)
end

@testset "Order three from an independent integer presentation" begin
    # Independent presentation of the rank two character block for exponent eight.
    # All pairs generating the dual have odd determinant. Ordering is forgotten.
    pairkey(a,b) = Tuple(sort([Tuple(mod.(a,8)),Tuple(mod.(b,8))]))
    chars = [(a,b) for a in 0:7 for b in 0:7]
    keys = sort(unique([pairkey(a,b) for a in chars for b in chars if isodd(a[1]*b[2]-a[2]*b[1])]))
    index = Dict(k=>i for (i,k) in enumerate(keys))
    R = zero_matrix(ZZ,2length(keys),length(keys))
    C = [0 -1; 1 -1]
    for (i,(aa,bb)) in enumerate(keys)
        a,b = collect(aa),collect(bb)
        R[i,i] += 1
        R[i,index[pairkey(a-b,b)]] -= 1
        R[i,index[pairkey(a,b-a)]] -= 1
        R[length(keys)+i,i] += 1
        R[length(keys)+i,index[pairkey(C*a,C*b)]] -= 1
    end
    v = zero_matrix(ZZ,1,length(keys))
    for (s,sign) in [(1,1),(3,-1)]
        v[1,index[pairkey([s,s],[0,-s])]] += sign
        v[1,index[pairkey([s,0],[-s,-s])]] += sign
    end
    println("independent block columns = ",length(keys))
    flush(stdout)
    @test !can_solve(R,v,side=:left)
    @test can_solve(R,3v,side=:left)
    flush(stdout)
    E = [1 0; 0 1]
    act = ToricAction([AffineTorusMap(E,[1//8,0]),AffineTorusMap(E,[0,-1//8]),AffineTorusMap(C,[0,0])],toric_fan_P2())
    G = act.G
    h,k = act.gens[1:2]
    # Mobius inversion isolates this block in the corrected presentation.
    # For A = C8 squared the only nonzero mu(K,A) occur at A, the three
    # index two subgroups, and 2A. Their values are 1, -1, and 2.
    function mobius_class(s)
        result = BCClass(G,2)
        for (hg,mu,diagonal) in [([h,k],1,false),([h^2,k],-1,false),([h,k^2],-1,false),([h*k,k^2],-1,true),([h^2,k^2],2,false)]
            for pair in ([[s,s],[0,-s]],[[s,0],[-s,-s]])
                weights = diagonal ? [[a+b,b] for (a,b) in pair] : pair
                push!(result,mu,BCSymbol(G,hg,[h,k],weights))
            end
        end
        result
    end
    x = mobius_class(1)-mobius_class(3)
    @test order(bc_image(x)) == 3
    @test bc_image(x) != -bc_image(x)
    f = hom(G,G,act.gens,[h^3,k^3,act.gens[3]])
    @test bc_image(bc_transport(x,f)) == -bc_image(x)
    @test bc_image(bc_transport(bc_transport(x,f),f)) == bc_image(x)
    cert = certificate_nonzero(bc_image(x))
    @test verify(cert)
    @test verify_with_group(cert)
    println("independently certified order three class and its sign action")
end
end
