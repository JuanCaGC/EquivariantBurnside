module TestStructureOscar
using Test, Oscar, EquivariantBurnside
const EB = EquivariantBurnside

pair_key(p) = (String(p[:Ydesc]), Int(p[:Ysize]), Int(p[:orbitsize]), Int(p[:stabsize]))
class_key(h) = (h.Hdesc, sort(h.d), h.classsize, h.Csize, h.Nsize,
                sort(pair_key.(h.pairs)))
summand_key(s) = (s.Hdesc, sort(s.d), s.Ydesc, s.Ysize, s.orbitsize,
                  s.stabsize, s.autsize, string(s.value))

@testset "OSCAR and GAP structure routes" begin
    makers = Function[() -> symmetric_group(k) for k in 3:6]
    append!(makers, [() -> alternating_group(5),
                    () -> dihedral_group(PermGroup, 10),
                    () -> small_group(27, 3),
                    () -> small_group(48, 3),
                    () -> general_linear_group(2, 3)])
    for mk in makers
        G = mk()
        a, b = bc_structure(G), bc_structure_gap(mk())
        @test a.order == b.order
        @test sort(class_key.(a.hclasses), by=string) == sort(class_key.(b.hclasses), by=string)
        for n in 2:3
            ra, rb = bc(a, n), bc(b, n)
            @test ra.total == rb.total
            @test sort(summand_key.(ra.summands), by=string) == sort(summand_key.(rb.summands), by=string)
        end
        # Check stored matrices against actual conjugates on OSCAR elements.
        # Products of stabilizer generators also detect a reversed action convention.
        hindex = 0
        for cl in subgroup_classes(G)
            H = representative(cl)
            order(H) > 1 && is_abelian(H) || continue
            hindex += 1
            hs = EB._independent_gens(H)
            N = first(normalizer(G, H))
            C = first(centralizer(G, H))
            Ys = EB._intermediate_groups(C, H)
            orbs = GAP.Globals.Orbits(gapobj(N), GAP.GapObj(gapobj.(Ys)), GAP.Globals.OnPoints)
            @test length(orbs) == length(a.hclasses[hindex].pairs)
            for (orb, p) in zip(orbs, a.hclasses[hindex].pairs)
                Y = first(Oscar._as_subgroup(C, orb[1]))
                S = first(normalizer(N, Y))
                gs = small_generating_set(S)
                nontrivial = filter(g -> any(h^g != h for h in hs), gs)
                @test length(nontrivial) == length(p[:mats])
                for (g, M) in zip(nontrivial, p[:mats])
                    for j in eachindex(hs)
                        @test hs[j]^g == prod(hs[i]^M[j][i] for i in eachindex(hs))
                    end
                end
                actions = vcat(gs, [g*k for g in gs for k in gs])
                for g in actions
                    M = EB._action_matrix(H, hs, g)
                    for j in eachindex(hs)
                        reconstructed = prod(hs[i]^M[j][i] for i in eachindex(hs))
                        @test hs[j]^g == inv(g)*hs[j]*g == reconstructed
                    end
                end
            end
        end
    end
    raw = GAP.Globals.SymmetricGroup(4)
    @test bc(bc_structure(raw), 2).total == bc(bc_structure(symmetric_group(4)), 2).total
    @test gapobj(raw) === raw
    @test Int(GAP.Globals.Size(gapobj(general_linear_group(2, 3)))) == 48
end
end
