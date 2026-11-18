function bc_structure_tom(n::Integer)
    load_gap!()
    GAP.Globals.Read(GAP.GapObj(joinpath(@__DIR__, "..", "gap", "bc_structure_tom.g")))
    t = @elapsed raw = GAP.gap_to_julia(GAP.Globals.BCStructureTom(n); recursive=true)
    hcl = HClass[]
    for h in raw
        push!(hcl, HClass(h[:Hdesc], Int.(h[:d]), String.(h[:Hgens]), Int(h[:classsize]),
                                  Int(h[:Csize]), Int(h[:Nsize]), h[:pairs]))
    end
    tom = GAP.Globals.TableOfMarks(GAP.GapObj("S$n"))
    return BCStruct("S$n", Int(GAP.Globals.Size(GAP.Globals.UnderlyingGroup(tom))), hcl, t)
end
