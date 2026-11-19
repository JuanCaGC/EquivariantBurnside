# ---------------------------------------------------------------------------
# Certificates of non-vanishing in BC_n(G)  (work package 1.3)
#
# A certificate states: for the block [H,Y] with character orders d, the functional f: Z^gens -> Z/q
# kills every relation of B_n(H)/(C) and f(class vector) is nonzero, so the class is nonzero.
# Format EBNZCERT 1, see handoff/SPEC_FASE1_2_1_3.md section 4.  Two verifiers:
#   `verify`            the standalone file verifier/verify_nonzero.jl (no packages, at most 150 lines),
#   `verify_with_group` rebuilds G from the certificate and re-derives the block data through OSCAR.
# What is NOT certified: that the symbols map to the class vector (trusted engine code).
# ---------------------------------------------------------------------------

include(joinpath("..", "verifier", "verify_nonzero.jl"))

"""
    group_fingerprint(G) -> String

SHA-256 (hex) of `"EB-GROUP-1\\n" * order * "\\n" * join(GAP strings of GeneratorsOfGroup, "\\n")`.
It binds a certificate to the given generating tuple of G, NOT to the isomorphism type of G.
"""
function group_fingerprint(G)
    Gg = gapobj(G)
    gs = [String(GAP.Globals.String(g)) for g in GAP.Globals.GeneratorsOfGroup(Gg)]
    text = "EB-GROUP-1\n" * string(Int(GAP.Globals.Size(Gg))) * "\n" * join(gs, "\n")
    return bytes2hex(SHA.sha256(text))
end

"""
    NonzeroCertificate

A certificate that an element of BC_n(G) is nonzero. Build it with `certificate_nonzero`, check it with
`verify` and `verify_with_group`, store it with `write_certificate` and `read_certificate`.
"""
struct NonzeroCertificate
    group_order::Int
    fingerprint::String
    n::Int
    hdesc::String
    ydesc::String
    d::Vector{Int}
    ysize::Int
    orbitsize::Int
    modulus::Int                                # 0 means the functional takes values in Z
    perms::Vector{Vector{Int}}
    gens::Vector{Vector{Int}}
    f::Vector{Int}
    class::Vector{Tuple{Int,Int}}               # (position in gens, coefficient)
    ggens::Vector{String}                       # generators of G as GAP strings, empty when not evaluable
    hgens::Vector{String}
    ygens::Vector{String}
    symbols::Vector{String}                     # audit trail
end

Base.:(==)(a::NonzeroCertificate, b::NonzeroCertificate) =
    all(getfield(a, k) == getfield(b, k) for k in fieldnames(NonzeroCertificate))

function Base.show(io::IO, c::NonzeroCertificate)
    print(io, "NonzeroCertificate(n=$(c.n), H=$(c.hdesc), Y=$(c.ydesc), d=$(c.d), modulus=$(c.modulus), ",
          "$(length(c.gens)) generators, $(length(c.class)) class terms)")
end

"""
    certificate_nonzero(x::BCElement) -> NonzeroCertificate

Certificate that `x` is nonzero, built from the first block (in sorted order) and the first coordinate
that is nonzero. Throws `ArgumentError` if `x` is zero.
"""
function certificate_nonzero(x::BCElement)
    is_zero(x) && throw(ArgumentError("element is zero: no certificate of non-vanishing exists"))
    key = bc_blocks(x)[1]
    a = x.blocks[key]
    j = findfirst(!=(0), a.coords)
    q = a.moduli[j]
    Q = a.bm.Qm
    f = [q == 0 ? Q[i, j] : mod(Q[i, j], q) for i in 1:size(Q, 1)]
    class = sort!([(a.bm.col[k], c) for (k, c) in a.classvec])
    val = sum((c * f[pos] for (pos, c) in class); init = 0)
    (q == 0 ? val : mod(val, q)) == a.coords[j] ||
        error("internal inconsistency: the functional does not reproduce the coordinate of the element")
    Gg = x.Ggap
    plain = GAP.Globals.IsPermGroup(Gg) || GAP.Globals.IsMatrixGroup(Gg)
    ggens = plain ? [String(GAP.Globals.String(g)) for g in GAP.Globals.GeneratorsOfGroup(Gg)] : String[]
    return NonzeroCertificate(Int(GAP.Globals.Size(Gg)), group_fingerprint(Gg), x.n, key.hdesc, key.ydesc, key.d,
                              key.ysize, key.orbitsize, q, a.perms, a.bm.gens, f, class, ggens,
                              a.info.hgens, a.info.ygens, x.terms)
end

# ----------------------------------------------------------------------------- text format

_clean(s) = replace(String(s), r"[\r\n]+" => " ")

function _cert_lines(c::NonzeroCertificate)
    L = String["EBNZCERT 1", "group_order $(c.group_order)", "group_fingerprint $(c.fingerprint)", "n $(c.n)",
               "block_hdesc $(_clean(c.hdesc))", "block_ydesc $(_clean(c.ydesc))",
               "block_d " * join(c.d, " "), "block_ysize $(c.ysize)", "block_orbitsize $(c.orbitsize)",
               "modulus $(c.modulus)", "nperms $(length(c.perms))"]
    append!(L, ["perm " * join(p, " ") for p in c.perms])
    push!(L, "ngens $(length(c.gens))")
    append!(L, ["gen " * join(g, " ") for g in c.gens])
    push!(L, "f " * join(c.f, " "), "nclass $(length(c.class))")
    append!(L, ["term $(pos) $(coef)" for (pos, coef) in c.class])
    append!(L, ["ggen " * _clean(s) for s in c.ggens])
    append!(L, ["bhgen " * _clean(s) for s in c.hgens])
    append!(L, ["bygen " * _clean(s) for s in c.ygens])
    append!(L, ["symbol " * _clean(s) for s in c.symbols])
    push!(L, "END")
    return L
end

"""Write the certificate as plain text (format EBNZCERT 1)."""
function write_certificate(path::AbstractString, c::NonzeroCertificate)
    open(path, "w") do io
        for l in _cert_lines(c)
            println(io, l)
        end
    end
    return path
end

_rest(l, key) = length(l) > length(key) ? String(l[length(key)+2:end]) : ""

"""Read a certificate written by `write_certificate`. Throws `ArgumentError` on a malformed file."""
function read_certificate(path::AbstractString)
    lines = readlines(path)
    (!isempty(lines) && strip(lines[1]) == "EBNZCERT 1") || throw(ArgumentError("not a certificate of format EBNZCERT 1"))
    any(strip(l) == "END" for l in lines) || throw(ArgumentError("truncated certificate: the END line is missing"))
    ints(l) = parse.(Int, split(l)[2:end])
    line1(key) = (i = findfirst(l -> startswith(l, key * " "), lines); i === nothing ?
                throw(ArgumentError("missing line $(key)")) : lines[i])
    many(key) = [l for l in lines if startswith(l, key * " ") || l == key]
    try
        return NonzeroCertificate(
            ints(line1("group_order"))[1], String(split(line1("group_fingerprint"))[2]), ints(line1("n"))[1],
            _rest(line1("block_hdesc"), "block_hdesc"), _rest(line1("block_ydesc"), "block_ydesc"),
            ints(line1("block_d")), ints(line1("block_ysize"))[1], ints(line1("block_orbitsize"))[1],
            ints(line1("modulus"))[1], [ints(l) for l in many("perm")], [ints(l) for l in many("gen")],
            ints(line1("f")), [(v = ints(l); (v[1], v[2])) for l in many("term")],
            [_rest(l, "ggen") for l in many("ggen")], [_rest(l, "bhgen") for l in many("bhgen")],
            [_rest(l, "bygen") for l in many("bygen")], [_rest(l, "symbol") for l in many("symbol")])
    catch e
        e isa ArgumentError && rethrow()
        throw(ArgumentError("malformed certificate: " * first(split(sprint(showerror, e), '\n'))))
    end
end

# ----------------------------------------------------------------------------- verifiers

"""
    verify(cert) -> Bool
    verify(path) -> Bool

Run the standalone verifier of `verifier/verify_nonzero.jl` on the certificate (or on a certificate file,
read as plain text without the parser of this package). `true` means the class vector is nonzero in
B_n(H)/(C) for the stated d, n and character permutations. It does not check that those permutations are
the stabilizer action of a group, see `verify_with_group`.
"""
verify(c::NonzeroCertificate) = first(NZVerifier.check(_cert_lines(c)))
verify(path::AbstractString) = first(NZVerifier.check(readlines(path)))

"""
    verify_with_group(cert) -> Bool

Rebuild G from the generator lines of the certificate, check its order and fingerprint, rebuild the block
representative H and Y~, check the orders, descriptions, |Y~| and orbit size, and recompute the action of
N_G(H) n N_G(Y~) on the characters of H through OSCAR (an intersection of two normalizers, a different
route from the GAP code of the engine). Returns `true` when the generated permutation group equals the one
of the certificate. It does not recompute the class vector from the symbols. Throws `ArgumentError` when
the certificate has no generators of G (groups whose elements cannot be written as plain GAP data).
"""
function verify_with_group(c::NonzeroCertificate)
    isempty(c.ggens) && throw(ArgumentError("the certificate has no group generators, cannot rebuild the group"))
    Gg = GAP.evalstr("Group(" * join(c.ggens, ", ") * ")")
    Int(GAP.Globals.Size(Gg)) == c.group_order || return false
    group_fingerprint(Gg) == c.fingerprint || return false
    G = Oscar._oscar_group(Gg)
    hs = [Oscar.group_element(G, GAP.evalstr(s)) for s in c.hgens]
    ys = [Oscar.group_element(G, GAP.evalstr(s)) for s in c.ygens]
    [order(Int, h) for h in hs] == c.d || return false
    H = first(sub(G, hs))
    Yt = first(sub(G, ys))
    issubset(H, Yt) || return false
    order(Int, Yt) == c.ysize || return false
    String(GAP.Globals.StructureDescription(gapobj(H))) == c.hdesc || return false
    ydesc = order(Int, Yt) <= 2000 ? String(GAP.Globals.StructureDescription(gapobj(Yt))) : "order $(order(Int, Yt))"
    ydesc == c.ydesc || return false
    NH = first(normalizer(G, H)); NY = first(normalizer(G, Yt))
    S = first(intersect(NH, NY))
    div(order(Int, NH), order(Int, S)) == c.orbitsize || return false
    # exponent vectors of every element of H in the basis hs
    expo = Dict{Any,Vector{Int}}()
    for t in Iterators.product((0:(dd - 1) for dd in c.d)...)
        expo[prod((hs[i]^t[i] for i in eachindex(hs)); init = one(G))] = collect(t)
    end
    ctx = CharCtx(c.d)
    newperms = Vector{Int}[]
    for g in gens(S)
        M = Matrix{Int}(undef, length(hs), length(hs))
        for j in eachindex(hs)
            M[j, :] = expo[hs[j]^g]
        end
        push!(newperms, char_perm(ctx, M))
    end
    idp = collect(1:ctx.m)
    close(ps) = (cl = perm_closure(filter(!=(idp), ps)); cl === nothing ? nothing : Set(vcat(cl, [idp])))
    a = close(c.perms); b = close(newperms)
    return a !== nothing && a == b
end
