# Shared inputs and independent expectations, written before implementation inspection.
using Test, EquivariantBurnside, Oscar
const EB = EquivariantBurnside
const GG = Oscar.GAP.Globals
matrix_group(code) = Oscar.GAP.evalstr(code)
elements(G) = collect(GG.Elements(G))
sizegroup(G) = Int(GG.Size(G))

const S3_CODE = "Group([[0,1,0],[1,0,0],[0,0,1]],[[0,1,0],[0,0,1],[1,0,0]])"
const A4_CODE = "Group(DiagonalMat([1,-1,-1]),[[0,1,0],[0,0,1],[1,0,0]])"
const S4_CODE = "Group(DiagonalMat([1,-1,-1]),[[0,1,0],[0,0,1],[1,0,0]],-[[0,1,0],[1,0,0],[0,0,1]])"
const Q8_CODE = "Group(DiagonalMat([E(4),-E(4)]),[[0,1],[-1,0]])"
const DIC16_CODE = "Group(DiagonalMat([E(8),E(8)^-1]),[[0,1],[-1,0]])"
const HEIS_CODE = "Group(DiagonalMat([1,E(3),E(3)^2]),[[0,1,0],[0,0,1],[1,0,0]])"
const C5_CODE = "Group(DiagonalMat([1,E(5),E(5)^2]))"

# GAP computes representations from character theory, with no package recursion involved.
function irreducible_three(code)
    matrix_group("(function() local g,r,v\u003b g := " * code *
        "\u003b for r in IrreducibleRepresentations(g) do v := Image(r)\u003b " *
        "if Length(One(v)) = 3 and Size(v) = Size(g) then return v\u003b fi\u003b od\u003b Error(\"no faithful degree three representation\")\u003b end)()")
end
function scalar_extension(G, n)
    gens = collect(GG.GeneratorsOfGroup(G))
    scalar = GG.E(n) * GG.One(G)
    GG.Group(Oscar.GAP.GapObj(vcat(gens, [scalar])))
end
