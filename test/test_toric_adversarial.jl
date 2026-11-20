module TestToricAdversarial
using Test, Oscar, EquivariantBurnside
const E = [1 0; 0 1]
const square = [[1,0],[0,1],[-1,0],[0,-1]]
function argument_error(f,phrase)
    err = try
        f()
        nothing
    catch e
        e
    end
    @test err isa ArgumentError
    @test err isa ArgumentError && occursin(phrase,sprint(showerror,err))
end

@testset "Affine arithmetic and rejected input" begin
    f = AffineTorusMap([0 -1; 1 -1],[1//3,1//5])
    g = AffineTorusMap(E,[1//7,1//11])
    @test (f*g).nu == f.nu*g.nu
    @test (f*g).t == mod.(f.t+f.nu*g.t,1)
    @test (f*g).t != (g*f).t
    argument_error(() -> AffineTorusMap([2 0; 0 1],[0,0]),"determinant")
    argument_error(() -> AffineTorusMap(ones(Int,3,3),[0,0]),"2 by 2")
    argument_error(() -> AffineTorusMap(E,[0]),"two coordinates")
    argument_error(() -> affine_group(AffineTorusMap[]),"at least one")
    G = cyclic_group(PermGroup,3)
    identity = AffineTorusMap(E,[0,0])
    argument_error(() -> ToricAction(G,[identity],toric_fan_P2()),"not faithful")
    argument_error(() -> ToricAction(G,[identity],toric_fan_P2(),convention=:other),"convention")
    argument_error(() -> ToricAction(G,AffineTorusMap[],toric_fan_P2()),"one affine map")
    argument_error(() -> ToricAction([AffineTorusMap(-E,[0,0])],toric_fan_P2()),"not invariant")
    argument_error(() -> ToricAction([identity],[[2,0],[0,1],[-1,-1]]),"not primitive")
    argument_error(() -> ToricAction([identity],reverse(toric_fan_P2())),"smooth cone")
    argument_error(() -> ToricAction([AffineTorusMap(E,[1//3,0])],[[1,0],[0,1]]),"fan")
    for nu in ([0 1; 1 0],[1 0; 0 -1])
        fan = nu == [0 1; 1 0] ? toric_fan_hexagon() : square
        act = ToricAction([AffineTorusMap(nu,[0,0])],fan)
        argument_error(() -> toric_class(act),"reflection")
    end
end

@testset "Projective plane and product geometry" begin
    for m in (3,5,7,8)
        a = AffineTorusMap(E,[1//m,0])
        act = ToricAction([a],toric_fan_P2())
        G = act.G
        h = only(act.gens)
        expected = BCClass(G,2)
        push!(expected,BCSymbol(G,[h],[],[[1]]))
        push!(expected,BCSymbol(G,[h],[],[[m-1],[m-1]]))
        actual = toric_class(act)
        @test bc_image(actual) == bc_image(expected)
        # Evaluate every formal character on the specified generator h.
        # This detects the opposite sign even when the total class vanishes.
        weights = Dict{Tuple,Int}()
        for (coefficient,symbol) in actual.terms
            exponent = only(j for j in 1:m-1 if gapobj(h)^j == only(symbol.hg))
            values = Tuple(sort([mod(only(b)*invmod(exponent,m),m) for b in symbol.betas]))
            weights[values] = get(weights,values,0)+coefficient
        end
        @test weights == Dict((1,)=>1,(m-1,m-1)=>1)
        product = ToricAction(G,[a],square)
        prod_expected = BCClass(G,2)
        push!(prod_expected,BCSymbol(G,[h],[],[[1]]))
        push!(prod_expected,BCSymbol(G,[h],[],[[m-1]]))
        @test bc_image(toric_class(product)) == bc_image(prod_expected)
        refined = ToricAction(G,[a],toric_fan_hexagon())
        @test bc_image(toric_class(act)) == bc_image(toric_class(refined))
        inverted = ToricAction(G,[AffineTorusMap(E,[-1//m,0])],[-r for r in toric_fan_P2()])
        @test bc_image(toric_class(act)) == bc_image(toric_class(inverted))
        P = [0 1; 1 0]
        # A determinant negative map reverses counterclockwise ordering.
        changed = ToricAction(G,[AffineTorusMap(E,[0,1//m])],reverse([P*r for r in toric_fan_P2()]))
        @test bc_image(toric_class(act)) == bc_image(toric_class(changed))
        k = m == 8 ? 3 : 2
        phi = hom(G,G,[h],[h^k])
        reparam = ToricAction(G,[AffineTorusMap(E,[invmod(k,m)//m,0])],toric_fan_P2())
        @test bc_image(bc_transport(expected,phi)) == bc_image(toric_class(reparam))
        println("P2 C",m," class order = ",order(bc_image(expected)))
    end
    for m in (3,5)
        maps = [AffineTorusMap(E,[1//m,0]),AffineTorusMap(E,[0,1//m])]
        act = ToricAction(maps,toric_fan_P2())
        G = act.G
        h,k = act.gens
        expected = BCClass(G,2)
        for (r,w) in [(h,1),(k,1),(h*k,m-1)]
            push!(expected,BCSymbol(G,[r],[h,k],[[w]]))
        end
        for weights in ([[1,0],[0,1]],[[-1,1],[-1,0]],[[0,-1],[1,-1]])
            push!(expected,BCSymbol(G,[h,k],[],weights))
        end
        @test bc_image(toric_class(act)) == bc_image(expected)
        @test bc_image(toric_class(ToricAction(G,maps,toric_fan_hexagon()))) == bc_image(expected)
        phi = hom(G,G,[h,k],[h^2,k^2])
        j = invmod(2,m)
        reparam = ToricAction(G,[AffineTorusMap(E,[j//m,0]),AffineTorusMap(E,[0,j//m])],toric_fan_P2())
        @test bc_image(bc_transport(expected,phi)) == bc_image(toric_class(reparam))
        println("P2 C",m," squared class order = ",order(bc_image(expected)))
    end
end

# Boundary characters are computed with the dual basis of each smooth cone.
# A cyclic rotation acts freely on rays and cones. Each orbit contributes once.
function rotation_boundary(act,R,fan,m)
    G = act.G
    h,k = act.gens[1:2]
    result = BCClass(G,2)
    seen = Set{Tuple{Int,Int}}()
    for i in eachindex(fan)
        v = fan[i]
        Tuple(v) in seen && continue
        w = fan[mod1(i+1,length(fan))]
        M = h^v[1]*k^v[2]
        push!(result,BCSymbol(G,[M],[h,k],[[1]]))
        beta = [[w[2],-w[1]],[-v[2],v[1]]]
        push!(result,BCSymbol(G,[h,k],[],beta))
        x = v
        while !(Tuple(x) in seen)
            push!(seen,Tuple(x))
            x = R*x
        end
    end
    result
end

@testset "Rotations with translations and boundary refinements" begin
    for (r,R,fan) in [(2,-E,toric_fan_hexagon()),
                      (3,[0 -1; 1 -1],toric_fan_hexagon()),
                      (4,[0 -1; 1 0],square),
                      (6,[1 -1; 1 0],toric_fan_hexagon())]
        # Subdivide every cone to ensure adjacent rays have different orbits.
        refined = Vector{Int}[]
        for i in eachindex(fan)
            push!(refined,fan[i])
            push!(refined,fan[i]+fan[mod1(i+1,length(fan))])
        end
        maps = [AffineTorusMap(E,[1//3,0]),AffineTorusMap(E,[0,1//3]),AffineTorusMap(R,[0,0])]
        act = ToricAction(maps,refined)
        @test order(act.G) == 9r
        expected = rotation_boundary(act,R,refined,3)
        @test bc_image(toric_class(act,refine=false)) == bc_image(expected)
        coarse = ToricAction(act.G,maps,fan)
        @test bc_image(toric_class(coarse)) == bc_image(expected)
        auto = equivariant_refinement(coarse)
        @test bc_image(toric_class(ToricAction(act.G,maps,auto),refine=false)) == bc_image(expected)
        # Local cyclic tangent weights of rotations are b and -b.
        # The isolated interior contributions vanish by relation V.
        c = act.gens[3]
        local_class = bc_image(BCSymbol(act.G,[c],[],[[1],[r-1]]),2)
        @test is_zero(local_class)
        blowup = BCClass(act.G,2)
        if r == 2
            push!(blowup,BCSymbol(act.G,[c],[],[[1]]))
        else
            push!(blowup,BCSymbol(act.G,[c],[],[[1],[r-2]]))
            push!(blowup,BCSymbol(act.G,[c],[],[[2],[r-1]]))
            if iseven(r)
                push!(blowup,BCSymbol(act.G,[c^(r÷2)],[c],[[1]]))
            end
        end
        @test bc_image(blowup) == local_class
    end
end

@testset "Inverse maps and the convention on generators" begin
    R = [0 -1; 1 -1]
    rotation = ToricAction([AffineTorusMap(R,[0,0])],toric_fan_P2())
    @test Set(Tuple(r) for r in equivariant_refinement(rotation)) == Set(Tuple(r) for r in toric_fan_hexagon())
    argument_error(() -> toric_class(rotation,refine=false),"one orbit span a cone")
    S = [0 1; 1 0]
    maps = [AffineTorusMap(R,[0,0]),AffineTorusMap(S,[0,0])]
    G, generators = affine_group(maps)
    invmaps = [AffineTorusMap(R^2,[0,0]),maps[2]]
    right = ToricAction(G,invmaps,toric_fan_hexagon(),convention=:right)
    @test order(right.G) == 6
    # The inverse generator assignment also extends on this presentation.
    left = ToricAction(G,invmaps,toric_fan_hexagon(),convention=:left)
    @test order(left.G) == 6
    @test R*S != S*R
    r,t = generators
    for i in 0:2, j in 0:1
        g = r^i*t^j
        @test right.images[g].nu == S^j * R^mod(-i,3)
        @test left.images[g].nu == R^mod(-i,3) * S^j
    end
    @test right.images[r*t].nu != left.images[r*t].nu
    # With the redundant generator rs, only the opposite convention works.
    G3, gg = affine_group(vcat(maps,[AffineTorusMap(R*S,[0,0])]))
    anti = [invmaps[1],invmaps[2],AffineTorusMap(S*R^2,[0,0])]
    @test ToricAction(G3,anti,toric_fan_hexagon(),convention=:right) isa ToricAction
    argument_error(() -> ToricAction(G3,anti,toric_fan_hexagon(),convention=:left),"homomorphism")
    a = AffineTorusMap(E,[1//5,0])
    A, aa = affine_group([a])
    for conv in (:left,:right)
        @test ToricAction(A,[AffineTorusMap(E,[-1//5,0])],toric_fan_P2(),convention=conv) isa ToricAction
    end
end
end
