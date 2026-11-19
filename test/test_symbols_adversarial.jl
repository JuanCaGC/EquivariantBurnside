module TestSymbolsAdversarial
using Test, Oscar, EquivariantBurnside
const B = EquivariantBurnside

function argument_error(f, phrase)
    @test_throws ArgumentError f()
    err = try
        f()
        nothing
    catch e
        e
    end
    @test err isa ArgumentError && occursin(phrase, sprint(showerror, err))
end

@testset "Adversarial symbols" begin
    s4 = symmetric_group(4)
    a = s4([2, 1, 3, 4])
    b = s4([1, 3, 2, 4])
    c4 = s4([2, 3, 4, 1])
    raw = GAP.Globals.SymmetricGroup(4)
    r = GAP.evalstr("(1,2,3,4)")
    mat = general_linear_group(2, 3)
    pc = small_group(27, 3)
    for g in (s4, mat, pc, raw)
        argument_error(() -> BCSymbol(g, [], [], [[1]]), "H is trivial")
    end
    argument_error(() -> BCSymbol(s4, [one(s4)], [], [[1]]), "H is trivial")
    argument_error(() -> BCSymbol(s4, [a, b], [], [[1, 1]]), "H is not abelian")
    argument_error(() -> BCSymbol(raw, [r, r^2], [], [[1, 1]]), "not independent")
    argument_error(() -> BCSymbol(s4, [a], [b], [[1]]), "does not centralize H")
    argument_error(() -> BCSymbol_preimage(s4, [c4], [c4^2], [[1]]), "does not contain H")
    for g in (mat, pc)
        h = first(filter(x -> !isone(x), gens(g)))
        argument_error(() -> BCSymbol(g, [h], [], [[1, 1]]), "wrong number of coordinates")
        argument_error(() -> BCSymbol(g, [h], [], [[Int(order(h))]]), "zero character")
    end
    argument_error(() -> push!(BCClass(raw, 2), BCSymbol(raw, [r], [], [[2]])), "do not generate")
    argument_error(() -> push!(BCClass(s4, 1), BCSymbol(s4, [a], [], [[1], [1]])), "more characters than n")
    argument_error(() -> push!(BCClass(s4, 2), BCSymbol(raw, [r], [], [[1]])), "different group")
    for n in (0, -1)
        argument_error(() -> BCClass(s4, n), "n must be positive")
    end
    argument_error(() -> certificate_nonzero(bc_image(BCClass(s4, 2))), "element is zero")

    s3 = GAP.Globals.SymmetricGroup(3)
    h3 = GAP.evalstr("(1,2,3)")
    d7 = GAP.evalstr("DihedralGroup(IsPermGroup,14)")
    h7 = GAP.evalstr("First(AsList(DihedralGroup(IsPermGroup,14)), x->Order(x)=7)")
    data = [(s3, h3, 2, [[1,1], [2,2], [1,2], [1]]),
            (d7, h7, 3, [[1,1,2], [2,4,6], [2,3,6]])]
    syms = Any[]
    baselines = Any[]
    for (g, h, n, weights) in data
        symbols = [BCSymbol(g, [h], [], [[x] for x in w]) for w in weights]
        images = [bc_image(s, n) for s in symbols]
        push!(syms, (symbols[1], n))
        push!(baselines, images[1])
        @test order(images[1]) == 2
        @test !is_zero(images[1])
        @test !iszero(images[1])
        @test !isempty(bc_blocks(images[1]))
        @test isempty(bc_blocks(images[1] - images[1]))
        @test images[1] == images[2]
        @test images[1] + images[2] == 2 * images[1]
        @test is_zero(images[1] - images[2])
        cls = BCClass(g, n)
        push!(cls, 0, symbols[1])
        @test is_zero(bc_image(cls))
        push!(cls, symbols[1])
        @test bc_image(cls) == images[1]
        @test bc_image(cls + symbols[2]) == images[1] + images[2]
        @test bc_image(cls - symbols[2]) == images[1] - images[2]
        @test bc_image(cls + cls) == 2 * images[1]
        @test bc_image(-cls) == -1 * images[1]
        @test bc_image(3 * cls) == 3 * images[1]
        @test bc_image(BCSymbol(g, [h], [h, h^2], [[x] for x in weights[1]]), n) == images[1]
        @test bc_image(BCSymbol_preimage(g, [h], [h], [[x] for x in weights[1]]), n) == images[1]
        oldcoords = []
        for (w, im) in zip(weights, images)
            terms = [(1, [h], [h], [[x] for x in w])]
            prepare!(g)
            push!(oldcoords, first(class_coords(g, n, terms)))
            @test order(im) == class_order(g, n, terms)
            @test is_zero(im) == class_is_zero(g, n, terms)
            for k in (-2, -1, 0, 1, 2, 3)
                terms_k = [(k, [h], [h], [[x] for x in w])]
                @test is_zero(k * im) == class_is_zero(g, n, terms_k)
                @test order(k * im) == class_order(g, n, terms_k)
            end
        end
        for i in eachindex(images), j in eachindex(images)
            @test (images[i] == images[j]) == (oldcoords[i] == oldcoords[j])
            terms = [(1, [h], [h], [[x] for x in weights[i]]),
                     (-1, [h], [h], [[x] for x in weights[j]])]
            @test is_zero(images[i] - images[j]) == class_is_zero(g, n, terms)
        end
    end
    for i in (1, 2, 1, 2)
        s, n = syms[i]
        @test bc_image(s, n) == baselines[i]
    end
end
end
