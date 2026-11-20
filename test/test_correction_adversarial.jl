module TestCorrectionAdversarial
using Test, Oscar, EquivariantBurnside
const B = EquivariantBurnside

@testset "Every defining relation with correction" begin
    # These include noncyclic abelian groups and a nonabelian central extension.
    groups = [("C4", GAP.Globals.CyclicGroup(4)),
              ("C6", GAP.Globals.CyclicGroup(6)),
              ("C8", GAP.Globals.CyclicGroup(8)),
              ("C2xC4", GAP.Globals.AbelianGroup(GAP.GapObj([2,4]))),
              ("C3xC3", GAP.Globals.AbelianGroup(GAP.GapObj([3,3]))),
              ("Q8", GAP.Globals.SmallGroup(8,4))]
    for (label,G) in groups, n in (2,3)
        P = B._direct_presentation(G,n)
        els = GAP.Globals.AsSSortedList(G)
        values = Vector{Any}(undef,length(P.col))
        for ((i,y,beta),col) in P.col
            sub = P.subs[i]
            chars = B.CharCtx(sub.d).chars
            s = BCSymbol(G,[els[j] for j in sub.gens],
                         [els[j] for j in P.allsubs[y]], [Int.(chars[b]) for b in beta])
            values[col] = bc_image(s,n)
        end
        @testset "$label dimension $n" begin
            for row in P.rows
                result = bc_image(BCClass(G,n))
                for (j,a) in row
                    result += a * values[j]
                end
                @test is_zero(result)
            end
        end
        println("definition ",label," n=",n," columns=",length(P.col)," rows=",length(P.rows)," kinds=",sort(unique(P.kinds)))
    end
end

@testset "Written blowup relations with the kernel term" begin
    for m in (4,6,8)
        G = cyclic_group(m)
        h = first(gens(G))
        # b1=1 and b2=-1 have kernel of difference of order two.
        # Theta2 is the divisor (C2,G,1). The left side vanishes by V.
        s(a,b) = BCSymbol(G,[h],[],[[mod(a,m)],[mod(b,m)]])
        lhs = bc_image(s(1,m-1),2)
        rhs = BCClass(G,2)
        push!(rhs,s(1,m-2))
        push!(rhs,s(2,m-1))
        push!(rhs,BCSymbol(G,[h^(m÷2)],[h],[[1]]))
        @test is_zero(lhs)
        @test lhs == bc_image(rhs)
        old = bc_image(rhs,blowup_correction=false)
        println("cyclic blowup m=",m," uncorrected defect order=",order(old))
        # The C2 divisor vanishes by the equal-weight relation followed by V.
        @test is_zero(old)
    end
    G = GAP.Globals.AbelianGroup(GAP.GapObj([4,2]))
    generators = GAP.Globals.GeneratorsOfGroup(G)
    h,k = generators[1],generators[2]
    # Independent weights (1,0) and (1,1) differ only on the C2 factor.
    # Their difference has kernel <h>, on which both restrict to 1.
    lhs = BCSymbol(G,[h,k],[],[[1,0],[1,1]])
    rhs = BCClass(G,2)
    push!(rhs,BCSymbol(G,[h,k],[],[[1,0],[0,1]]))
    push!(rhs,BCSymbol(G,[h,k],[],[[0,1],[1,1]]))
    push!(rhs,BCSymbol(G,[h],[k],[[1]]))
    @test bc_image(lhs,2) == bc_image(rhs)
    @test bc_image(lhs,2,blowup_correction=false) != bc_image(rhs,blowup_correction=false)
    # In C9 the difference 4-1 has a kernel C3 with a nonzero divisor.
    G9 = cyclic_group(PermGroup,9)
    h9 = only(gens(G9))
    term(a,b) = BCSymbol(G9,[h9],[],[[a],[b]])
    before = term(1,4)
    after = BCClass(G9,2)
    push!(after,term(1,3))
    push!(after,term(6,4))
    theta = BCSymbol(G9,[h9^3],[h9],[[1]])
    push!(after,theta)
    @test bc_image(before,2) == bc_image(after)
    @test bc_image(before,2,blowup_correction=false) != bc_image(after,blowup_correction=false)
    @test order(bc_image(theta,2)) === nothing

end
end
