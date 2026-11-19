# Standalone checker for non-vanishing certificates (format EBNZCERT 1). Pure Julia, no packages.
# Usage: julia verify_nonzero.jl cert.txt   (prints VALID or INVALID: reason, exit code 0 iff valid)
#
# Soundness statement. If this prints VALID, the class vector of the certificate is nonzero in B_n(H)/(C)
# for the stated orders d, the stated n and the stated permutations of characters. It does NOT check that
# the permutations are the stabilizer action of a group, nor that symbols map to the class vector.
# Character index of c = (c_1..c_k): 1 + sum c_i*stride_i, stride_1 = 1, stride_i = stride_{i-1}*d_{i-1}.
# Index 1 is the zero character. Relations of B_n(H)/(C), for a sorted n-tuple beta and positions i < j
# with a = beta_i, b = beta_j (tuples are re-sorted after each substitution):
#   a = b = 0: none.   a = b != 0: beta = beta with position j set to 0, and beta = 0 when 2a = 0.
#   a != b, both nonzero: beta = 0 when a + b = 0, and beta = beta1 + beta2 with a -> a-b, b -> b-a.
#   exactly one zero: none.   (C): beta = sort(p(beta)) for each permutation p.
module NZVerifier

struct Bad <: Exception; msg::String; end
bad(msg) = throw(Bad(msg))

function check(lines::Vector{String})
    try
        return (_check(lines), "")
    catch e
        e isa Bad && return (false, e.msg)
        return (false, "malformed certificate: " * first(split(sprint(showerror, e), '\n')))
    end
end

# Generators (sorted n-tuples whose nonzero entries generate the dual) and relation rows of B_n(H)/(C).
function relations(n, d, perms)
    m = prod(d); k = length(d)
    stride = [prod(d[1:i-1]; init = 1) for i in 1:k]
    dec(a) = [((a - 1) ÷ stride[i]) % d[i] for i in 1:k]
    enc(c) = 1 + sum(mod(c[i], d[i]) * stride[i] for i in 1:k)
    add(a, b) = enc(dec(a) .+ dec(b)); neg(a) = enc(.-dec(a))
    function generates(t)
        seen = falses(m); seen[1] = true; stack = [1]; nz = unique(filter(!=(1), t))
        while !isempty(stack)
            x = pop!(stack)
            for g in nz; y = add(x, g); seen[y] || (seen[y] = true; push!(stack, y)); end
        end
        return all(seen)
    end
    gens = Vector{Int}[]
    function rec(pos, lo, cur)
        pos > n && (generates(cur) && push!(gens, copy(cur)); return)
        for x in lo:m; push!(cur, x); rec(pos + 1, x, cur); pop!(cur); end
    end
    rec(1, 1, Int[])
    rels = Vector{Pair{Vector{Int},Int}}[]
    for β in gens
        for i in 1:n-1, j in i+1:n
            a, b = β[i], β[j]
            if a == 1 || b == 1
                continue
            elseif a == b
                β0 = copy(β); β0[j] = 1
                push!(rels, [β => 1, β0 => -1]); neg(a) == a && push!(rels, [β => 1])
            else
                add(a, b) == 1 && push!(rels, [β => 1])
                β1 = copy(β); β1[i] = add(a, neg(b)); β2 = copy(β); β2[j] = add(b, neg(a))
                push!(rels, [β => 1, β1 => -1, β2 => -1])
            end
        end
        for p in perms
            βg = sort([p[x] for x in β]); βg != β && push!(rels, [β => 1, βg => -1])
        end
    end
    return gens, rels
end

function _check(lines)
    (!isempty(lines) && strip(lines[1]) == "EBNZCERT 1") || bad("missing header EBNZCERT 1")
    n = 0; q = -1; d = Int[]; f = Int[]; perms = Vector{Int}[]; gens = Vector{Int}[]; terms = Tuple{Int,Int}[]
    cnt = Dict("nperms" => -1, "ngens" => -1, "nclass" => -1); ended = false
    for l in lines[2:end]
        w = split(l); isempty(w) && continue
        t = w[1]; v = t in ("block_d", "perm", "gen", "f", "term", "n", "modulus", "nperms", "ngens", "nclass") ? parse.(Int, w[2:end]) : Int[]
        t == "n" && (n = v[1]); t == "block_d" && (d = v); t == "modulus" && (q = v[1]); t == "f" && (f = v)
        haskey(cnt, t) && (cnt[t] = v[1])
        t == "perm" && push!(perms, v); t == "gen" && push!(gens, v); t == "term" && push!(terms, (v[1], v[2]))
        t == "END" && (ended = true)
    end
    ended || bad("missing END")
    n >= 1 && q >= 0 && !isempty(d) && all(>=(1), d) || bad("bad n, modulus or block_d")
    (length(perms), length(gens)) == (cnt["nperms"], cnt["ngens"]) && length(terms) == cnt["nclass"] || bad("line counts do not match")
    m = prod(d); k = length(d)
    stride = [prod(d[1:i-1]; init = 1) for i in 1:k]
    dec(a) = [((a - 1) ÷ stride[i]) % d[i] for i in 1:k]
    enc(c) = 1 + sum(mod(c[i], d[i]) * stride[i] for i in 1:k)
    add(a, b) = enc(dec(a) .+ dec(b)); neg(a) = enc(.-dec(a))
    for p in perms
        length(p) == m && sort(p) == 1:m && p[1] == 1 || bad("a perm is not a permutation fixing the zero character")
        all(p[add(a, b)] == add(p[a], p[b]) for a in 1:m, b in 1:m) || bad("a perm is not additive on characters")
    end
    gens_exp, rels = relations(n, d, perms)
    gens == gens_exp || bad("the gen lines are not the generators of B_n(H) in lexicographic order")
    N = length(gens); length(f) == N || bad("f has the wrong length")
    col = Dict(g => i for (i, g) in enumerate(gens))
    red(x) = q == 0 ? x : mod(x, q)
    ev(row) = red(sum(c * f[col[sort(t)]] for (t, c) in row))
    all(ev(r) == 0 for r in rels) || bad("f does not kill every relation")
    all(1 <= pos <= N && c != 0 for (pos, c) in terms) || bad("a class term has a bad position or a zero coefficient")
    red(sum((c * f[pos] for (pos, c) in terms); init = 0)) != 0 || bad("f of the class vector is zero")
    return true
end

if abspath(PROGRAM_FILE) == @__FILE__
    ok, msg = check(readlines(ARGS[1]))
    println(ok ? "VALID" : "INVALID: " * msg)
    exit(ok ? 0 : 1)
end
end # module
