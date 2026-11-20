module TestToricLociAdversarial
using Test, Oscar, EquivariantBurnside
const E = [1 0; 0 1]
const C = [0 -1; 1 -1]
const S = [-1 1; 0 1]
det2(M) = M[1,1]*M[2,2]-M[1,2]*M[2,1]
rank2(x,y) = any(x[i]*y[j] != x[j]*y[i] for i in 1:4 for j in 1:4)
modpoint(u) = mod.(u, 1)
fixed(f, u) = modpoint(f.nu * u + f.t) == u
onlayer(l, u) = mod(sum(l.m .* u) - l.c, 1) == 0

@testset "Fixed sets from rational congruences" begin
    cases = [
        (E, [0,0], :all, -1),
        (E, [1//3,0], :points, 0),
        (-E, [0,0], :points, 4),
        (-E, [1//3,1//2], :points, 4),
        (C, [0,0], :points, 3),
        ([0 -1; 1 0], [0,0], :points, 2),
        ([1 -1; 1 0], [0,0], :points, 1),
        ([0 1; 1 0], [0,0], :layers, 1),
        ([0 1; 1 0], [1//3,-1//3], :layers, 1),
        ([0 1; 1 0], [1//3,1//3], :layers, 0),
        ([1 0; 0 -1], [0,0], :layers, 2),
        ([1 0; 0 -1], [0,1//3], :layers, 2),
        ([1 0; 0 -1], [1//2,0], :layers, 0)]
    for (nu, t, kind, count) in cases
        f = AffineTorusMap(nu, t)
        result = fixed_set(f)
        @test result[1] == kind
        kind == :all || @test length(result[2]) == count
        for a in 0:11, b in 0:11
            u = [a//12, b//12]
            reported = result[1] == :all || (result[1] == :points ? u in result[2] : any(l -> onlayer(l,u), result[2]))
            @test reported == fixed(f,u)
        end
        if result[1] == :points
            @test all(u -> fixed(f,u), result[2])
        elseif result[1] == :layers
            for l in result[2]
                @test gcd(l.m...) == 1
                @test any(onlayer(l, [a//12,b//12]) for a in 0:11 for b in 0:11)
            end
        end
    end
    l = FixedLayer([1,-1], 1//3)
    @test onlayer(l, [1//3,0])
    @test !onlayer(l, [0,1//3])
end

# Write t1 = u and t2 = v-u and t3 = -v.
# The six points are the identity, the three nonzero 2-torsion points,
# and the two central cube roots (u,v) = (a,2a).
@testset "Inversion and permutations on the determinant one torus" begin
    expected = Set([(0//1,0//1), (1//2,0//1), (0//1,1//2),
                    (1//2,1//2), (1//3,2//3), (2//3,1//3)])
    maps = [AffineTorusMap(C,[0,0]), AffineTorusMap(S,[0,0]), AffineTorusMap(-E,[0,0])]
    act = ToricAction(maps, toric_fan_hexagon())
    @test order(act.G) == 12
    curves = fixed_curves(act)
    pts = special_points(act)
    @test length(curves) == 6
    @test all(length(c.H) == 2 for c in curves)
    @test Set(Tuple(p.u) for p in pts) == expected
    @test sort([length(p.stabilizer) for p in pts]) == [4,4,4,6,6,12]
    @test sort([p.orbit for p in pts if p.rep]) == [1,2,3]
    q = [1//5,1//7]
    shifted = ToricAction([AffineTorusMap(f.nu,q-f.nu*q) for f in maps],toric_fan_hexagon())
    @test Set(Tuple(p.u) for p in special_points(shifted)) == Set(Tuple(modpoint(collect(u)+q)) for u in expected)
    @test sort([length(p.stabilizer) for p in special_points(shifted)]) == [4,4,4,6,6,12]
    for c in curves, a in 0:11, b in 0:11
        u = [a//12,b//12]
        if onlayer(c.layer,u)
            @test all(fixed(act.images[h],u) for h in c.H)
        end
    end
    # Add all 2-torsion translations through the rotation orbit of (1/2,0).
    extended = ToricAction(vcat(maps,[AffineTorusMap(E,[1//2,0])]), toric_fan_hexagon())
    @test order(extended.G) == 48
    linear = [C^i * S^j * (-E)^k for i in 0:2 for j in 0:1 for k in 0:1]
    affine = [AffineTorusMap(nu,[a//2,b//2]) for nu in linear for a in 0:1 for b in 0:1]
    candidates = Set{Tuple{Rational{Int},Rational{Int}}}()
    for a in 0:11, b in 0:11
        u = [a//12,b//12]
        st = filter(f -> fixed(f,u), affine)
        isolated = any(f -> det2(f.nu-E) != 0, st)
        normals = [Tuple(vec(f.nu-E)) for f in st if f.nu != E && det2(f.nu-E) == 0]
        intersecting = any(rank2(collect(x),collect(y)) for x in normals for y in normals)
        (isolated || intersecting) && push!(candidates,Tuple(u))
    end
    extended_points = special_points(extended)
    @test Set(Tuple(p.u) for p in extended_points) == candidates
    # Multiplication by two descends to the original action.
    # Every original special point has four lifts.
    lifts = Set(Tuple(modpoint((collect(u)+[a,b])/2)) for u in expected for a in 0:1 for b in 0:1)
    @test Set(Tuple(p.u) for p in extended_points) == lifts
    @test sort([p.orbit for p in extended_points if p.rep]) == [4,8,12]
    extra_curves = fixed_curves(extended)
    @test length(extra_curves) == 12
    @test all(length(c.H) == 2 for c in extra_curves)
    for a in 0:11, b in 0:11
        u = [a//12,b//12]
        expected_curve = any(f.nu != E && det2(f.nu-E) == 0 && fixed(f,u) for f in affine)
        @test any(onlayer(c.layer,u) for c in extra_curves) == expected_curve
    end
    for p in extended_points
        count = sum(fixed(f,p.u) for f in affine)
        @test length(p.stabilizer) == count
        @test p.orbit * count == 48
    end
    println("loci extended points = ",length(extended_points)," curves = ",length(fixed_curves(extended)))
end

end
