module TestDcp
using Test
using EquivariantBurnside.DCP
using Oscar
using Printf
const gg = GAP.Globals
const failures = Ref(0)
const known = Ref(0)
function check(label, ok, detail="")
    @testset "$label" begin
        @test ok
    end
    println(ok ? "PASS " : "FAIL ", label, isempty(detail) ? "" : " | "*detail)
    flush(stdout)
    ok || (failures[] += 1)
    ok
end

# Compare complete tuples of characters up to an explicitly permitted change
# of independent generators. The image in (Q/Z)^r is invariant under that
# change and remembers all relations among the ordered characters.
function charimage(orders, chars)
    L = foldl(lcm, orders; init=1)
    xs = Iterators.product((0:d-1 for d in orders)...)
    sort(unique(vec([Tuple(mod(sum(c[j]*x[j]*(L÷orders[j]) for j in eachindex(orders); init=0),L)//L
        for c in chars) for x in xs])))
end
samechars(c, orders, chars) = charimage(c.basis_orders,c.characters)==charimage(orders,chars)
char1(xs...) = [[x] for x in xs]
zchars(r) = [Int[] for _ in 1:r]

function groupname(G)
    n=Int(gg.Size(G))
    if n==2
        g=first(x for x in DCP.gvec(gg.Elements(G)) if Int(gg.Order(x))==2)
        return Int(gg.TraceMat(g))==1 ? "S2" : "diag"
    elseif n==4
        return Bool(gg.IsCyclic(G)) ? "C4" : "S2xS2"
    end
    get(Dict(24=>"S4",8=>"D8",6=>"S3",3=>"C3",1=>"1"),n,string(n))
end
function deltaname(c)
    if c.delta_order==4 && !Bool(gg.IsCyclic(c.delta))
        return all(Int(gg.Order(g))==1 || Int(gg.TraceMat(g)) == -1 for g in DCP.gvec(gg.Elements(c.delta))) ? "K4" : "S2xS2"
    end
    groupname(c.delta)
end
function dump(label,A,cs)
    println("DATA ",label," elements=",length(A.elements)," classes=",length(A.orbit_indices),
        " scalar_order=",gg.Size(A.raw.scalar)," arrangement_seconds=",round(A.seconds,digits=3))
    for (i,c) in enumerate(cs)
        println("ROW ",i," groups=",[Int(gg.Size(g)) for g in c.groups],
            " dims=",[Int(gg.Length(s)) for s in c.subspaces]," N=",c.normalizer_order,
            " Delta=",c.delta_description," basis_orders=",c.basis_orders,
            " chars=",c.characters," normal=",c.normal_characters)
        println("  BASIS ",String.(gg.String.(c.basis_generators)))
        println("  SPACES ",String.(gg.String.(c.subspaces)))
    end
    check(label*" generic stabilizers central in flag normalizers",
        all(c->Bool(gg.IsSubgroup(gg.Center(c.normalizer),c.delta)),cs))
    check(label*" characters jointly faithful",
        all(c->length(charimage(c.basis_orders,c.characters))==c.delta_order,cs))
    check(label*" flag orbit sizes account for every flag",begin
        eligible=[i for i in eachindex(A.elements) if A.projective ?
            0<Int(A.elements[i].dimension)<A.dimension : Int(A.elements[i].order)>1]
        countfrom(i)=1+sum(countfrom(j) for j in eligible if
            Int(A.elements[j].dimension)>Int(A.elements[i].dimension) &&
            Bool(gg.DCP_Contains(A.elements[j].basis,A.elements[i].basis));init=0)
        actual=sum(countfrom(i) for i in eligible;init=0)
        actual==sum(Int(gg.Size(A.raw.group))÷c.normalizer_order for c in cs;init=0)
    end)
    flush(stdout)
end

function validate_s4()
    G=standard_symmetric(4)
    A=arrangement(G;projective=false); cs=chains(A); dump("S4 affine",A,cs)
    check("KT Table 1 row count",length(cs)==11)
    expected=[
        (["S4"],1,Int[],zchars(1)),
        (["S2xS2"],2,[2],char1(1)),
        (["S3"],1,Int[],zchars(1)),
        (["S2"],2,[2],char1(1)),
        (["S4","S2xS2"],2,[2],char1(0,1)),
        (["S4","S3"],1,Int[],zchars(2)),
        (["S4","S2"],2,[2],char1(0,1)),
        (["S2xS2","S2"],4,[2,2],[[0,1],[1,0]]),
        (["S3","S2"],2,[2],char1(0,1)),
        (["S4","S2xS2","S2"],4,[2,2],[[0,0],[0,1],[1,0]]),
        (["S4","S3","S2"],2,[2],char1(0,0,1))]
    for (i,(names,d,ords,ch)) in enumerate(expected)
        hits=filter(c->groupname.(c.groups)==names,cs)
        delta=["1","diag","1","S2","diag","1","S2","S2xS2","S2","S2xS2","S2"][i]
        N=[24,8,6,4,8,6,4,4,2,4,2][i]
        check("KT Table 1 row $i",length(hits)==1 && only(hits).delta_order==d &&
            deltaname(only(hits))==delta && only(hits).normalizer_order==N && samechars(only(hits),ords,ch))
    end
    A=arrangement(G); cs=chains(A); dump("S4 projective",A,cs)
    check("KT Table 2 row count",length(cs)==13)
    expected=[
        (["S3"],1,Int[],zchars(2)),
        (["S2"],2,[2],char1(0,1)),
        (["D8"],2,[2],char1(0,1)),
        (["diag"],2,[2],char1(1,0)),
        (["S2xS2"],2,[2],char1(1,0)),
        (["C3"],1,Int[],zchars(2)),
        (["C4"],1,Int[],zchars(2)),
        (["S3","S2"],2,[2],char1(0,0,1)),
        (["D8","S2"],4,[2,2],[[0,0],[0,1],[1,0]]),
        (["D8","diag"],4,[2,2],[[0,1],[1,1],[1,0]]),
        (["S2xS2","S2"],4,[2,2],[[1,0],[0,0],[0,1]]),
        (["S2xS2","diag"],4,[2,2],[[1,0],[0,1],[0,0]]),
        (["C4","diag"],4,[4],char1(1,3,2))]
    for (i,(names,d,ords,ch)) in enumerate(expected)
        hits=filter(c->groupname.(c.groups)==names,cs)
        delta=["1","S2","diag","diag","S2","1","1","S2","S2xS2","K4","S2xS2","S2xS2","C4"][i]
        N=[6,4,8,8,4,3,4,2,4,4,4,4,4][i]
        check("KT Table 2 row $i",length(hits)==1 && only(hits).delta_order==d &&
            deltaname(only(hits))==delta && only(hits).normalizer_order==N && samechars(only(hits),ords,ch))
    end
    check("KT Table 2 row 10 Delta is normal Klein four",begin
        c=only(filter(c->groupname.(c.groups)==["D8","diag"],cs))
        all(Int(gg.Order(g))==1 || Int(gg.TraceMat(g)) == -1 for g in DCP.gvec(gg.Elements(c.delta)))
    end)
    A,cs
end

# Proposition 9.2 counted independently by labeled partitions and cyclic
# orders of equal blocks. This calculation never calls the arrangement code.
function ipart(n,lo=1)
    n==0 && return [Int[]]
    [vcat(i,p) for i in lo:n for p in ipart(n-i,i)]
end
function prop92(n)
    total=big(0); classes=0
    for p in ipart(n)
        length(p)==1 && continue
        length(p)==2 && p[1]==p[2] && continue
        denom=prod(factorial(big(x)) for x in p)*prod(factorial(big(count(==(x),p))) for x in unique(p))
        total+=factorial(big(n))÷denom; classes+=1
    end
    for e in 2:n, q in 1:n÷e, p in ipart(q)
        z=n-e*q
        denom=factorial(big(z))*prod(factorial(big(x))^e*e for x in p)*
            prod(factorial(big(count(==(x),p))) for x in unique(p))
        total+=factorial(big(n))÷denom; classes+=1
    end
    (Int(total)+1,classes+1)
end

function validate_sn()
    for n in 3:6
        A=arrangement(standard_symmetric(n))
        got=(length(A.elements)+1,length(A.orbit_indices)+1)
        want=prop92(n)
        check("KT Proposition 9.2 S$n full lattice including infinity",got==want,
            "computed=$got predicted=$want seconds=$(round(A.seconds,digits=3))")
    end
end

function validate_eb()
    G=GAP.evalstr("Group(DiagonalMat([1,E(3),E(3)]),DiagonalMat([1,E(5),E(5)^-1]),[[1,0,0],[0,0,1],[0,1,0]])")
    A=arrangement(G); cs=chains(A); dump("C3 x D5",A,cs)
    check("EB Table 5 row count",length(cs)==11)
    expected=[([30],30,3,[0]),([15],15,1,Int[]),([6],6,2,[1]),
        ([6],6,1,Int[]),([3],30,3,[1]),([2],6,2,[0]),
        ([30,2],6,6,[0,4]),([15,3],15,15,[4,1]),
        ([6,3],6,6,[1,4]),([6,3],6,6,[4,1]),([6,2],6,6,[4,0])]
    used=Set{Int}()
    for (i,(orders,N,d,prefix)) in enumerate(expected)
        hits=Int[]
        for (j,c) in enumerate(cs)
            j in used && continue
            Int.(gg.Size.(c.groups))==orders && c.normalizer_order==N && c.delta_order==d || continue
            ok = isempty(prefix) || charimage(c.basis_orders,c.characters[1:length(prefix)])==charimage([d],char1(prefix...))
            ok && push!(hits,j)
        end
        ok=length(hits)==1
        check("EB Table 5 row $i printed character prefix",ok)
        ok && push!(used,only(hits))
    end
    G=GAP.evalstr("Group(DiagonalMat([E(7),E(7)^-1,E(7)^2,E(7)^-2]),[[0,1,0,0],[1,0,0,0],[0,0,0,1],[0,0,1,0]])")
    A=arrangement(G); cs=chains(A); dump("D7",A,cs)
    check("EB Table 6 row count",length(cs)==4)
    for (i,eps) in enumerate([0,1])
        hits=filter(c->Int(gg.Size(c.groups[1]))==2 && c.characters==char1(eps,1-eps),cs)
        check("EB Table 6 row $i",length(hits)==1 && only(hits).normalizer_order==2 && only(hits).delta_order==2)
    end
    rot=GAP.evalstr("DiagonalMat([E(7),E(7)^-1,E(7)^2,E(7)^-2])")
    values=Int[]
    for c in cs
        Int(gg.Size(c.groups[1]))==7 || continue
        val=gg.DCP_Scalar(c.subspaces[1],rot)
        exponent=only(a for a in 0:6 if gg.E(7)^a==val)
        push!(values,min(exponent,7-exponent))
        check("EB Table 6 C7 Delta and normalizer for eigen-orbit $exponent",c.delta_order==1 && c.normalizer_order==7 && all(isempty,c.characters))
    end
    # The printed 2,3 use a different primitive generator, or are erroneous.
    # Under r -> r^2 our ±1,±2 become ±2,±3, simultaneously.
    mapped=sort([min(mod(2*a,7),mod(-2*a,7)) for a in values])
    # Preserve the documented discrepancy for the displayed rotation basis.
    @test_broken sort(values)==[2,3]
    if sort(values)!=[2,3]
        known[]+=1
        println("FAIL EB Table 6 literal C7 characters relative to displayed rotation | documented basis discrepancy: computed $(sort(values)), printed [2, 3]")
    end
    check("EB Table 6 rows 3 and 4 after explicit generator change r -> r^2",mapped==[2,3],
        "input rotation gives $(sort(values)), changed rotation gives $mapped")
    for (row,want) in [(3,2),(4,3)]
        check("EB Table 6 row $row Gamma-character after r -> r^2",count(==(want),mapped)==1)
    end
end

function validate_extra()
    G=GAP.evalstr("Group(DiagonalMat([1,E(3),E(3)^2]))")
    A=arrangement(G); cs=chains(A)
    check("diagonal C3 projective three isolated eigenspaces",length(A.elements)==4 && length(cs)==3 &&
        all(c->c.delta_order==1 && c.normalizer_order==3,cs))
    A=arrangement(G;projective=false); cs=chains(A)
    check("diagonal C3 affine fixed axis only",length(A.elements)==2 && length(cs)==1 && only(cs).delta_order==1)
    G=GAP.evalstr("Group(DiagonalMat([-1,1,1]),DiagonalMat([1,-1,1]))")
    A=arrangement(G); cs=chains(A)
    check("diagonal C2 squared projective coordinate arrangement",length(A.elements)==7 && length(cs)==12 &&
        count(c->length(c.indices)==1,cs)==6 && count(c->length(c.indices)==2,cs)==6 &&
        all(c->c.delta_order==(length(c.indices)==1 ? 2 : 4),cs))
    G=GAP.evalstr("Group(DiagonalMat([E(3),E(3)]))")
    A=arrangement(G); cs=chains(A)
    check("nontrivial scalar C3 projective empty boundary",Int(gg.Size(A.raw.scalar))==3 && length(A.elements)==1 && isempty(cs))
    A=arrangement(G;projective=false); cs=chains(A)
    check("scalar C3 affine origin divisor",length(cs)==1 && only(cs).delta_order==3 &&
        samechars(only(cs),[3],char1(1)))
    G=GAP.evalstr("Group(DiagonalMat([E(3),-E(3)]))")
    A=arrangement(G); cs=chains(A)
    check("C6 with scalar C3 and two projective boundary components",
        Int(gg.Size(A.raw.scalar))==3 && length(A.elements)==3 && length(cs)==2 &&
        all(c->c.delta_order==6 && c.normalizer_order==6 && c.normal_characters==char1(3),cs) &&
        count(c->samechars(c,[6],char1(2,5)),cs)==1 &&
        count(c->samechars(c,[6],char1(5,2)),cs)==1)
end

function main()
    println("Julia ",VERSION," OSCAR ",pkgversion(Oscar)," GAP ",String(GAP.evalstr("GAPInfo.Version")))
    for (name,run) in [("S4 tables",validate_s4),("EB tables",validate_eb),("Sn counts",validate_sn),("independent diagonal examples",validate_extra)]
        t=time()
        try
            run()
        catch e
            check(name*" exception",false,sprint(showerror,e,catch_backtrace()))
        end
        @printf("TIME %s %.3f seconds\n",name,time()-t)
        flush(stdout)
    end
    println("SUMMARY unexpected_failures=",failures[]," documented_basis_discrepancies=",known[])
    failures[]==0
end
main()
end
