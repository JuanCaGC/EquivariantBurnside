module TestToricReflectionsAdversarial
using Test, Oscar, EquivariantBurnside
const EB = EquivariantBurnside
const E = [1 0; 0 1]
const S = [0 1; 1 0]
const D = [1 0; 0 -1]
const square = [[1,0],[0,1],[-1,0],[0,-1]]
const a2 = [[1,0],[0,1],[-1,1],[-1,0],[0,-1],[1,-1]]
det2(M) = M[1,1]*M[2,2]-M[1,2]*M[2,1]
wedge(v,w) = v[1]*w[2]-v[2]*w[1]
point(u) = Tuple(mod.(u,1))

# Independent closure retains the word in the specified OSCAR generators.
# No multiplication or image lookup in the affine implementation is used.
function closure(act, maps)
    out = [(E, Rational{Int}[0,0], one(act.G))]
    seen = Set([(Tuple(vec(E)),(0//1,0//1))])
    j = 1
    while j <= length(out)
        M,t,g = out[j]
        for (f,h) in zip(maps,act.gens)
            A,b = M*f.nu, mod.(t+M*f.t,1)
            key = (Tuple(vec(A)),Tuple(b))
            if !(key in seen)
                push!(seen,key)
                push!(out,(A,b,g*h))
            end
        end
        j += 1
    end
    @test length(out) == Int(order(act.G))
    for (M,t,g) in out
        @test act.images[g].nu == M
        @test act.images[g].t == t
    end
    out
end

# For a rank one fixed equation choose its primitive normal. Enumerating c
# on a sufficiently divisible grid solves the remaining congruences exactly.
function grid_oracle(group,N)
    grid = [[i//N,j//N] for i in 0:N-1 for j in 0:N-1]
    fixes(M,t,u) = point(M*u+t) == point(u)
    layers = Dict{Tuple,Set{Any}}()
    isolated = Set{Tuple}()
    for (M,t,g) in group
        A = M-E
        if det2(A) != 0
            union!(isolated,(point(u) for u in grid if fixes(M,t,u)))
        elseif A != zeros(Int,2,2)
            row = A[findfirst(i -> any(!iszero,A[i,:]),1:2),:]
            m = div.(row,gcd(row...))
            m[findfirst(!iszero,m)] < 0 && (m = -m)
            for c in (i//N for i in 0:N-1)
                sample = [u for u in grid if mod(sum(m.*u),1)==c]
                if all(u -> fixes(M,t,u),sample)
                    key = (Tuple(m),c)
                    layers[key] = Set(h for (B,s,h) in group if all(u -> fixes(B,s,u),sample))
                end
            end
        end
    end
    special = copy(isolated)
    for u in grid
        normals = [m for ((m,c),_) in layers if mod(sum(collect(m).*u),1)==c]
        any(wedge(collect(m),collect(n)) != 0 for m in normals for n in normals) && push!(special,point(u))
    end
    data = Dict(u => (Set(g for (M,t,g) in group if fixes(M,t,collect(u))),
                     Set(point(M*collect(u)+t) for (M,t,g) in group)) for u in special)
    layers,data
end

function cases()
    z = [0,0]
    [ ("single",[AffineTorusMap(D,z)],square,12),
      ("Klein",[AffineTorusMap(D,z),AffineTorusMap(-D,z)],square,12),
      ("D4",[AffineTorusMap(S,z),AffineTorusMap(D,z)],square,12),
      ("D4 translated",[AffineTorusMap(S,z),AffineTorusMap(D,z),AffineTorusMap(E,[1//3,0])],square,12),
      ("C2 times S3",[AffineTorusMap(S,z),AffineTorusMap([0 1; -1 -1],z),AffineTorusMap(-E,z)],a2,12),
      ("glide fifth",[AffineTorusMap(D,[1//5,0])],square,20),
      ("glide and half",[AffineTorusMap(D,[1//5,0]),AffineTorusMap(E,[0,1//2])],square,20) ]
end

@testset "Independent fixed equations and fan geometry" begin
    for (name,maps,fan,N) in cases()
        @testset "$name" begin
            act = ToricAction(maps,fan)
            group = closure(act,maps)
            layers,pts = grid_oracle(group,N)
            # Doubling the grid checks completeness of the rational enumeration.
            layers2,pts2 = grid_oracle(group,2N)
            @test layers == layers2
            @test pts == pts2
            curves = fixed_curves(act)
            actual = Dict((Tuple(c.layer.m),c.layer.c) => Set(c.H) for c in curves)
            @test actual == layers
            sp = special_points(act)
            @test Set(point(p.u) for p in sp) == Set(keys(pts))
            for p in sp
                H,orb = pts[point(p.u)]
                @test Set(p.stabilizer) == H
                @test p.orbit == length(orb)
                @test count(q -> q.rep && point(q.u) in orb,sp) == 1
            end
            rays = equivariant_refinement(act)
            rs = Set(Tuple(v) for v in rays)
            @test length(rs) == length(rays)
            @test all(gcd(v...)==1 for v in rays)
            @test all(wedge(rays[i],rays[mod1(i+1,length(rays))])==1 for i in eachindex(rays))
            # Positive determinants and exactly one full turn certify completeness.
            turn = sum(mod(atan(w[2],w[1])-atan(v[2],v[1]),2pi) for (v,w) in zip(rays,circshift(rays,-1)))
            @test isapprox(turn,2pi)
            @test all(Tuple(M*v) in rs for (M,t,g) in group for v in rays)
            @test all(all(M*rays[i] != rays[mod1(i+1,length(rays))] for (M,t,g) in group) for i in eachindex(rays))
            for ((m,c),H) in layers
                v = [m[2],-m[1]]
                @test Tuple(v) in rs
                @test Tuple(-v) in rs
            end
            println(name," curves=",length(layers)," special points=",length(pts)," orbits=",count(p->p.rep,sp)," refined rays=",length(rays))
            flush(stdout)
        end
    end
    # Inversion of every generator converts a left action into a right action.
    # Check all elements, including products with noncommuting linear parts.
    maps = [AffineTorusMap(S,[0,0]),AffineTorusMap(D,[0,0]),AffineTorusMap(E,[1//3,0])]
    act = ToricAction(maps,square)
    group = closure(act,maps)
    invmaps = [AffineTorusMap(div.([f.nu[2,2] -f.nu[1,2]; -f.nu[2,1] f.nu[1,1]],det2(f.nu)),
                  -div.([f.nu[2,2] -f.nu[1,2]; -f.nu[2,1] f.nu[1,1]],det2(f.nu))*f.t) for f in maps]
    right = ToricAction(act.G,invmaps,square,convention=:right)
    for (M,t,g) in group
        @test right.images[inv(g)].nu == M
        @test right.images[inv(g)].t == t
    end
    glide = AffineTorusMap(D,[1//5,0])
    @test isempty(last(fixed_set(glide)))
end
# Translate the public character convention into presentation columns.
function formal_vector(cls,P)
    Gg = gapobj(cls.G)
    els = GAP.Globals.AsSSortedList(Gg)
    pos(x) = Int(GAP.Globals.Position(els,x))
    plist(gs) = sort([pos(x) for x in GAP.Globals.AsSSortedList(GAP.Globals.Subgroup(Gg,GAP.GapObj(gs)))])
    subidx = Dict(s.elts=>i for (i,s) in enumerate(P.subs))
    allidx = Dict(s=>i for (i,s) in enumerate(P.allsubs))
    v = zeros(Int,length(P.col))
    for (coef,sym) in cls.terms
        i = subidx[plist(sym.hg)]
        y = allidx[plist(vcat(sym.hg,sym.yg))]
        exps = Dict{Int,Vector{Int}}()
        for e in Iterators.product((0:o-1 for o in sym.ords)...)
            g = GAP.Globals.One(Gg)
            for (h,k) in zip(sym.hg,e)
                g = g*h^k
            end
            exps[pos(g)] = collect(e)
        end
        st = P.subs[i]
        ctx = EB.CharCtx(st.d)
        beta = Int[]
        for b in sym.betas
            c = [mod(Int(sum(b[j]*exps[g][j]//sym.ords[j] for j in eachindex(b))*st.d[k]),st.d[k]) for (k,g) in enumerate(st.gens)]
            push!(beta,EB.encode(ctx,c))
        end
        v[P.col[(i,y,sort(beta))]] += coef
    end
    v
end

# Canonical integer row lattices, not ranks over a field.
function in_relations(P,v,kinds)
    rows = [r for (r,k) in zip(P.rows,P.kinds) if k in kinds]
    A = zero_matrix(ZZ,length(rows)+1,length(v))
    for (i,r) in enumerate(rows), (j,c) in r
        A[i,j] = c
    end
    H = hnf(A)
    for j in eachindex(v)
        A[length(rows)+1,j] = v[j]
    end
    hnf(A) == H
end
const VC = [:V,:C]
const VCE = [:V,:C,:B_equal]
const ALLREL = [:V,:C,:B_equal,:B_distinct,:B_distinct_theta2]

# Blow up a diagonal tangent representation. Its two charts have weights
# (b,c-b) and (b-c,c). Scalar elements give the exceptional divisor.
function blowup!(cls,a,r,b,c)
    push!(cls,BCSymbol(cls.G,[a,r],[],[b,c-b]))
    push!(cls,BCSymbol(cls.G,[a,r],[],[b-c,c]))
    if b[2] == c[2] == 1
        push!(cls,BCSymbol(cls.G,[r],[a,r],[[1]]))
    end
end

function diagonal_expected(act,half=false)
    # f=(D,(1/5,0)) has order ten. f^6 translates by 1/5 and f^5 reflects.
    f = act.gens[1]
    a,r = f^6,f^5
    G = act.G
    ys = collect(act.gens)
    cls,curves = BCClass(G,2),BCClass(G,2)
    for sign in (1,-1)
        push!(cls,BCSymbol(G,[a],ys,[[sign]]))
    end
    if half
        b = act.gens[2]
        # The vertical half translation fixes its boundary divisor and makes
        # the old toric corners isolated strata with stabilizer C5 times C2.
        push!(cls,BCSymbol(G,[b],[a,b],[[1]]))
        for sign in (1,-1)
            push!(cls,BCSymbol(G,[a,b],[],[[sign,0],[0,1]]))
        end
    end
    reflections = half ? [r,act.gens[2]*r] : [r,r]
    for h in reflections
        push!(curves,BCSymbol(G,[h],[a,h],[[1]]))
        for sign in (1,-1)
            blowup!(cls,a,h,[sign,0],[0,1])
        end
    end
    cls+curves,curves
end

@testset "Hand classes with fifth translations" begin
    for half in (false,true)
        maps = [AffineTorusMap(D,[1//5,0])]
        half && push!(maps,AffineTorusMap(E,[0,1//2]))
        act = ToricAction(maps,square)
        expected,curves = diagonal_expected(act,half)
        P = EB._direct_presentation(act.G,2)
        actual = toric_class(act)
        v = formal_vector(actual-expected,P)
        @test in_relations(P,v,VC)
        @test bc_image(actual) == bc_image(expected)
        omitted = formal_vector(curves,P)
        @test !in_relations(P,omitted,VC)
        @test in_relations(P,omitted,VCE)
        @test is_zero(bc_image(curves))
        # Reversing a fifth character must remain visible before blowup relations.
        a = act.gens[1]^6
        positive = BCClass(act.G,2)
        negative = BCClass(act.G,2)
        push!(positive,BCSymbol(act.G,[a],collect(act.gens),[[1]]))
        push!(negative,BCSymbol(act.G,[a],collect(act.gens),[[-1]]))
        @test !in_relations(P,formal_vector(positive-negative,P),VC)
        println("diagonal half=",half," formal difference VC=",in_relations(P,v,VC)," expected terms=",length(expected.terms))
    end
    maps = [AffineTorusMap(S,[1//5,1//5])]
    act = ToricAction(maps,toric_fan_P2())
    f = act.gens[1]
    a,r = f^6,f^5
    expected = BCClass(act.G,2)
    push!(expected,BCSymbol(act.G,[r],[a,r],[[1]]))
    for sign in (1,-1)
        push!(expected,BCSymbol(act.G,[a],[a,r],[[sign]]))
        # On the boundary coordinate q=t2/t1, swap acts by inversion.
        # At q=1 its normal eigenvalue is +1, at q=-1 it is -1.
        for parity in (0,1)
            blowup!(expected,a,r,[sign,parity],[0,1])
        end
    end
    P = EB._direct_presentation(act.G,2)
    actual = toric_class(act)
    @test in_relations(P,formal_vector(actual-expected,P),VC)
    @test bc_image(actual) == bc_image(expected)
    exceptional = BCClass(act.G,2)
    push!(exceptional,2,BCSymbol(act.G,[r],[a,r],[[1]]))
    @test !in_relations(P,formal_vector(exceptional,P),VC)
    @test in_relations(P,formal_vector(exceptional,P),VCE)
    println("swap fifth expected terms=",length(expected.terms))
    flush(stdout)
end

@testset "Hand class for inversion and coordinate permutations" begin
    maps = [AffineTorusMap(S,[0,0]),AffineTorusMap([0 1; -1 -1],[0,0]),AffineTorusMap(-E,[0,0])]
    act = ToricAction(maps,a2)
    r,c,z = act.gens
    expected = BCClass(act.G,2)
    curves = BCClass(act.G,2)
    for h in (r,z*r)
        # Two orbits of mirrors, centralizer of each is the Klein group.
        push!(curves,BCSymbol(act.G,[h],[z,r],[[1]]))
        # Boundary inversion points have scalar tangent action.
        push!(expected,BCSymbol(act.G,[h],[],[[1]]))
        # At the identity and the nonzero two torsion orbit, eigenlines
        # have Klein stabilizer with radial and projective weights.
        push!(expected,2,BCSymbol(act.G,[z,h],[],[[1,0],[0,1]]))
    end
    # Exceptional divisors over the identity and the two torsion orbit.
    push!(expected,BCSymbol(act.G,[z],collect(act.gens),[[1]]))
    push!(expected,BCSymbol(act.G,[z],[z,r],[[1]]))
    # Complex eigenlines at the identity have cyclic stabilizer of order six.
    push!(expected,BCSymbol(act.G,[z*c],[],[[1],[4]]))
    # At the nonzero three torsion orbit, eigenlines have stabilizer C3.
    push!(expected,BCSymbol(act.G,[c],[],[[1],[1]]))
    expected = expected+curves
    P = EB._direct_presentation(act.G,2)
    actual = toric_class(act)
    v = formal_vector(actual-expected,P)
    @test in_relations(P,v,VC)
    @test in_relations(P,v,ALLREL)
    @test bc_image(actual) == bc_image(expected)
    @test !in_relations(P,formal_vector(curves,P),VC)
    @test in_relations(P,formal_vector(curves,P),VCE)
    println("C2 times S3 expected terms=",length(expected.terms)," image order=",order(bc_image(expected)))
end

@testset "Changing the fan and actual extra centers" begin
    maps = [AffineTorusMap(D,[1//5,0])]
    act = ToricAction(maps,square)
    f = act.gens[1]
    a,r = f^6,f^5
    # Blow up the four toric corners, a nontrivial change of the boundary.
    octagon = Vector{Int}[]
    for i in eachindex(square)
        push!(octagon,square[i],square[i]+square[mod1(i+1,4)])
    end
    other = ToricAction(act.G,maps,octagon)
    x,y = toric_class(act),toric_class(other)
    P = EB._direct_presentation(act.G,2)
    @test Set(Tuple(v) for v in act.rays) != Set(Tuple(v) for v in other.rays)
    @test bc_image(x) == bc_image(y)
    @test in_relations(P,formal_vector(x-y,P),ALLREL)
    # Each corner has tangent weights (+1,0) or (-1,0) for C5.
    # Its blowup creates a point with weights (sign,-sign), killed by V.
    # The free symbol lattice still detects omission of these points.
    corner_terms = BCClass(act.G,2)
    for sign in (1,-1)
        push!(corner_terms,BCSymbol(act.G,[a],[],[[sign],[-sign]]))
    end
    @test any(!iszero,formal_vector(corner_terms,P))
    @test in_relations(P,formal_vector(corner_terms,P),VC)
    @test formal_vector(y-x,P) == formal_vector(corner_terms,P)
    # This new torus orbit lies on v=0 and is disjoint from the boundary.
    # Blowing it up has one new point with the two odd C2 weights.
    extra = [[1//7,0//1]]
    blown = toric_class(act,extra_points=extra)
    added = BCClass(act.G,2)
    push!(added,BCSymbol(act.G,[r],[],[[1],[1]]))
    @test any(!iszero,formal_vector(added,P))
    @test formal_vector(blown-x,P) == formal_vector(added,P)
    @test in_relations(P,formal_vector(added,P),VC)
    @test bc_image(blown) == bc_image(x)
    # Sensitivity before V is necessary here because BC2 kills this orbit.
    @test formal_vector(blown-added,P) != formal_vector(blown,P)
    # A second model comparison has genuine sensitivity in BC2. Full
    # fifth translations make the new ray carry a C5 divisor symbol.
    fullmaps = [AffineTorusMap(E,[1//5,0]),AffineTorusMap(E,[0,1//5]),AffineTorusMap(D,[0,0])]
    full = ToricAction(fullmaps,square)
    aa,bb,rr = full.gens
    changedfan = [[1,0],[1,1],[0,1],[-1,0],[0,-1],[1,-1]]
    changed = ToricAction(full.G,fullmaps,changedfan)
    basecls,newcls = toric_class(full),toric_class(changed)
    exceptional = BCClass(full.G,2)
    push!(exceptional,BCSymbol(full.G,[aa*bb],[aa,bb],[[1]]))
    # Read the normal character on the specified generator ab, rather than
    # on whichever cyclic generator the output happens to select.
    weights = Dict{Int,Int}()
    target = gapobj(aa*bb)
    for (coef,sym) in newcls.terms
        length(sym.hg)==1 && sym.ords==[5] && length(sym.betas)==1 || continue
        h = only(sym.hg)
        conjugate = gapobj(rr)*h*gapobj(rr)^-1
        exponent = findfirst(k -> h^k == target || conjugate^k == target,1:4)
        exponent === nothing && continue
        weight = mod(only(only(sym.betas))*exponent,5)
        weights[weight] = get(weights,weight,0)+coef
    end
    @test weights == Dict(1=>1)
    @test weights != Dict(4=>1)
    @test bc_image(basecls) == bc_image(newcls)
    @test !is_zero(bc_image(exceptional))
    @test bc_image(newcls-exceptional) != bc_image(basecls)
    println("model sensitivity: omitted C5 exceptional divisor nonzero=",!is_zero(bc_image(exceptional))," order=",order(bc_image(exceptional)))
    println("extra point sensitivity: nonzero free symbol, zero modulo V")
end

@testset "Options and invalid arguments" begin
    for (name,maps,fan,N) in cases()
        act = ToricAction(maps,fan)
        auto = toric_class(act,points=:auto)
        @test bc_image(auto) == bc_image(toric_class(act,points=true))
        @test_throws ArgumentError toric_class(act,points=false)
        @test_throws ArgumentError toric_class(act,points=:invalid)
        refined = equivariant_refinement(act)
        good = ToricAction(act.G,maps,refined)
        @test bc_image(auto) == bc_image(toric_class(good,refine=false))
    end
    swap = ToricAction([AffineTorusMap(S,[0,0])],toric_fan_P2())
    @test_throws ArgumentError toric_class(swap,refine=false)
    # This square also lacks the fixed direction (1,1).
    swap_square = ToricAction([AffineTorusMap(S,[0,0])],square)
    @test_throws ArgumentError toric_class(swap_square,refine=false)
    act = ToricAction([AffineTorusMap(D,[1//5,0])],square)
    # The specification does not promise an exception type for extra_points.
    # A one-coordinate vector is incompatible with the two-dimensional
    # affine operation, as also witnessed by independent multiplication.
    @test_throws DimensionMismatch E*Rational{Int}[0]
    @test_throws DimensionMismatch toric_class(act,extra_points=[[0//1]])
    @test_throws ArgumentError ToricAction([AffineTorusMap(D,[0,0])],toric_fan_P2())
    # Nonreflecting controls distinguish auto, true and false semantics.
    translation = ToricAction([AffineTorusMap(E,[1//5,0])],square)
    @test bc_image(toric_class(translation,points=false)) == bc_image(toric_class(translation,points=:auto))
    @test bc_image(toric_class(translation,points=true)) == bc_image(toric_class(translation,points=:auto))
end
end
