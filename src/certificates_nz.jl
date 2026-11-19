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
    group_fingerprint(G)

Fingerprint a group with its chosen generating tuple.

The argument `G` is an OSCAR or GAP group. Returns a 64-character hexadecimal string.

`group_fingerprint(G)` is the SHA-256 hex of the text "EB-GROUP-1\\n" * order * "\\n" * the GAP strings of `GeneratorsOfGroup(G)` joined by newlines. It binds a certificate to the given generating tuple and NOT to the isomorphism type.

# Examples

```jldoctest
G = symmetric_group(3)
println(length(group_fingerprint(G)))
println(group_fingerprint(G) == group_fingerprint(gapobj(G)))

# output

64
true
```
"""
function group_fingerprint(G)
    Gg = gapobj(G)
    gs = [String(GAP.Globals.String(g)) for g in GAP.Globals.GeneratorsOfGroup(Gg)]
    text = "EB-GROUP-1\n" * string(Int(GAP.Globals.Size(Gg))) * "\n" * join(gs, "\n")
    return bytes2hex(SHA.sha256(text))
end

"""
    NonzeroCertificate

Store a functional witnessing a nonzero block vector.

Obtain this return type from `certificate_nonzero(x)`. Its fields record the group order and fingerprint, dimension, block descriptions and orders, character permutations and multisets, functional `f`, class coefficients and generator strings. The integer `modulus` is zero for a functional valued in Z. The `symbols` field is an audit trail, not a checked derivation. Prefer the factory and file reader to direct field construction.

A certificate that an element of BC_n(G) is nonzero. Build it with `certificate_nonzero`, check it with
`verify` and `verify_with_group`, store it with `write_certificate` and `read_certificate`.

What a non-vanishing certificate does and does not prove. `verify` checks, in plain integer arithmetic and without Oscar, that the stated functional f kills every relation of B_n(H)/(C) regenerated from d, n and the stated permutations of characters, and that f of the class vector is nonzero. If it returns true the class vector is nonzero in B_n(H)/(C) for those data. It does NOT check that the permutations are the stabilizer action of the group, nor that the symbols map to the class vector. `verify_with_group` rebuilds the group from the certificate and re-derives the block data and the permutations through different OSCAR calls than the engine, but it does not recompute the class vector from the symbols.

# Examples

```jldoctest
S3 = symmetric_group(3)
c3 = cperm(S3, [1,2,3])
s = BCSymbol(S3, [c3], [c3], [[1],[1]])
x = bc_image(s, 2)
cert = certificate_nonzero(x)
println(cert isa NonzeroCertificate)
println(cert.modulus)

# output

true
2
```
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
    certificate_nonzero(x::BCElement)

Construct a non-vanishing certificate for an evaluated class.

The argument `x` must be a nonzero `BCElement`. Returns a `NonzeroCertificate`, selecting the first sorted nonzero block and its first nonzero Smith coordinate. Throws `ArgumentError` for zero.

Certificate that `x` is nonzero, built from the first block (in sorted order) and the first coordinate
that is nonzero. Throws `ArgumentError` if `x` is zero.

# Examples

```jldoctest
S3 = symmetric_group(3)
c3 = cperm(S3, [1,2,3])
s = BCSymbol(S3, [c3], [c3], [[1],[1]])
x = bc_image(s, 2)
cert = certificate_nonzero(x)
println(verify(cert))

# output

true
```
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

"""
    write_certificate(path, cert)

Write a certificate in the plain text EBNZCERT 1 format.

The arguments are a file path `path::AbstractString` and a `NonzeroCertificate` named `cert`. Creates or overwrites the file and returns `path`.

Write the certificate as plain text (format EBNZCERT 1).

# Examples

```jldoctest
S3 = symmetric_group(3)
c3 = cperm(S3, [1,2,3])
s = BCSymbol(S3, [c3], [c3], [[1],[1]])
x = bc_image(s, 2)
cert = certificate_nonzero(x)
mktempdir() do dir
    path = joinpath(dir, "point.cert")
    println(write_certificate(path, cert) == path)
    println(verify(path))
end

# output

true
true
```
"""
function write_certificate(path::AbstractString, c::NonzeroCertificate)
    open(path, "w") do io
        for l in _cert_lines(c)
            println(io, l)
        end
    end
    return path
end

_rest(l, key) = length(l) > length(key) ? String(l[length(key)+2:end]) : ""

"""
    read_certificate(path)

Read a certificate from the EBNZCERT 1 format.

The argument `path::AbstractString` names an existing file. Returns a `NonzeroCertificate`. Throws `ArgumentError` for malformed content. Reading does not verify the certificate.

Read a certificate written by `write_certificate`. Throws `ArgumentError` on a malformed file.

# Examples

```jldoctest
S3 = symmetric_group(3)
c3 = cperm(S3, [1,2,3])
s = BCSymbol(S3, [c3], [c3], [[1],[1]])
x = bc_image(s, 2)
cert = certificate_nonzero(x)
mktempdir() do dir
    path = joinpath(dir, "point.cert")
    write_certificate(path, cert)
    println(read_certificate(path) == cert)
end

# output

true
```
"""
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
    verify(cert)
    verify(path)

Check the integer non-vanishing witness.

Pass a `NonzeroCertificate` or a file path. Returns a boolean from the standalone verifier. The path form reads plain text directly without the package parser.

verify(cert) -> Bool
    verify(path) -> Bool

Run the standalone verifier of `verifier/verify_nonzero.jl` on the certificate (or on a certificate file,
read as plain text without the parser of this package). `true` means the class vector is nonzero in
B_n(H)/(C) for the stated d, n and character permutations. It does not check that those permutations are
the stabilizer action of a group, see `verify_with_group`.

What a non-vanishing certificate does and does not prove. `verify` checks, in plain integer arithmetic and without Oscar, that the stated functional f kills every relation of B_n(H)/(C) regenerated from d, n and the stated permutations of characters, and that f of the class vector is nonzero. If it returns true the class vector is nonzero in B_n(H)/(C) for those data. It does NOT check that the permutations are the stabilizer action of the group, nor that the symbols map to the class vector. `verify_with_group` rebuilds the group from the certificate and re-derives the block data and the permutations through different OSCAR calls than the engine, but it does not recompute the class vector from the symbols.

# Examples

```jldoctest
S3 = symmetric_group(3)
c3 = cperm(S3, [1,2,3])
s = BCSymbol(S3, [c3], [c3], [[1],[1]])
x = bc_image(s, 2)
cert = certificate_nonzero(x)
println(verify(cert))

# output

true
```
"""
verify(c::NonzeroCertificate) = first(NZVerifier.check(_cert_lines(c)))
verify(path::AbstractString) = first(NZVerifier.check(readlines(path)))

"""
    verify_with_group(cert)

Check the group and block data of a certificate through OSCAR.

The argument `cert` is a `NonzeroCertificate`. Returns a boolean comparing the rebuilt block action with the recorded action. This is a group-data check, use `verify(cert)` as well for the integer witness. Throws `ArgumentError` if group generator strings are absent. Only use trusted certificate generator strings, which are evaluated as GAP expressions.

Rebuild G from the generator lines of the certificate, check its order and fingerprint, rebuild the block
representative H and Y~, check the orders, descriptions, |Y~| and orbit size, and recompute the action of
N_G(H) n N_G(Y~) on the characters of H through OSCAR (an intersection of two normalizers, a different
route from the GAP code of the engine). Returns `true` when the generated permutation group equals the one
of the certificate. It does not recompute the class vector from the symbols. Throws `ArgumentError` when
the certificate has no generators of G (groups whose elements cannot be written as plain GAP data).

What a non-vanishing certificate does and does not prove. `verify` checks, in plain integer arithmetic and without Oscar, that the stated functional f kills every relation of B_n(H)/(C) regenerated from d, n and the stated permutations of characters, and that f of the class vector is nonzero. If it returns true the class vector is nonzero in B_n(H)/(C) for those data. It does NOT check that the permutations are the stabilizer action of the group, nor that the symbols map to the class vector. `verify_with_group` rebuilds the group from the certificate and re-derives the block data and the permutations through different OSCAR calls than the engine, but it does not recompute the class vector from the symbols.

# Examples

```jldoctest
S3 = symmetric_group(3)
c3 = cperm(S3, [1,2,3])
s = BCSymbol(S3, [c3], [c3], [[1],[1]])
x = bc_image(s, 2)
cert = certificate_nonzero(x)
println(verify_with_group(cert))

# output

true
```
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
