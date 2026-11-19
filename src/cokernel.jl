
# ---------------------------------------------------------------------------
# Cokernel of an integer relation matrix: sparse unit-pivot elimination + SNF
# ---------------------------------------------------------------------------

const Row = Dict{Int,Int}

"""
    certify_snf(rows, ncols)

Produce an exact Smith normal form certificate.

The argument `rows` is a vector of `Dict{Int,Int}` sparse rows with 1-based column indices and `ncols` is a nonnegative column count. Returns integer matrices `(A, U, V, D)` satisfying `U*A*V == D`.

Build the original integer relation matrix (one row per input relation, including
zero rows) and return a Smith certificate: `U*A*V == D`, with square unimodular
`U` and `V`. No unit-pivot elimination is used and `rows` is not mutated.
All matrices are over arbitrary-precision `ZZ`. Intended for small/moderate
presentations: the dense left transform has `length(rows)^2` entries.

Independently check the product, `abs(det(U)) == abs(det(V)) == 1`, diagonality,
and divisibility of successive nonzero diagonal entries of `D` (zeros last).
If its rank is r, the row cokernel has free rank `ncols-r`, diagonal entries
of absolute value > 1 give the cyclic torsion factors. Call before passing rows
to `cokernel_group`, which mutates its input. Use `show(stdout, "text/plain", A)`
(and similarly U, V, D) to display the returned certificate.

# Examples

```jldoctest
A, U, V, D = certify_snf([Dict(1 => 2), Dict(2 => 2)], 2)
println(U * A * V == D)
println((D[1,1], D[2,2]))

# output

true
(2, 2)
```
"""
function certify_snf(rows::Vector{Row}, ncols::Int)
    ncols >= 0 || throw(ArgumentError("ncols must be nonnegative"))
    A = zero_matrix(ZZ, length(rows), ncols)
    for (i, row) in enumerate(rows), (j, value) in row
        1 <= j <= ncols || throw(ArgumentError("relation column $j outside 1:$ncols"))
        A[i, j] = ZZ(value)
    end
    D, U, V = snf_with_transform(A)
    return A, U, V, D
end

"""
Z^ncols / <rows>.  Repeatedly uses a relation with a coefficient +-1 to
eliminate a generator (this does not change the quotient), then finishes the
small remaining matrix with Smith normal form over Z (Nemo/FLINT).
The elimination uses overflow-checked machine integers: a row operation that
would overflow is skipped (never wrapped), so the result is exact, an invariant
factor that does not fit in `Int` raises an error that says so.
Returns (AbGroup, remaining_dense_size).
"""
function cokernel_group(rows::Vector{Row}, ncols::Int)
    colrows = Dict{Int,Set{Int}}()
    for (r, row) in enumerate(rows), c in keys(row)
        push!(get!(colrows, c, Set{Int}()), r)
    end
    alive = trues(length(rows))
    updates = Tuple{Int,Int}[]
    neliminated = 0
    changed = true
    while changed
        changed = false
        for r in sortperm(length.(rows))
            alive[r] || continue
            row = rows[r]
            if isempty(row)
                alive[r] = false
                continue
            end
            best = 0; bestcnt = typemax(Int)
            for (c, v) in row
                if abs(v) == 1
                    cnt = length(colrows[c])
                    if cnt < bestcnt
                        best = c; bestcnt = cnt
                    end
                end
            end
            best == 0 && continue
            c = best; ε = row[c]
            # Exactness: entries are machine integers, so every product and difference is
            # computed with overflow checks.  The new row is computed first and only then
            # written.  If one entry would overflow, that row operation is not done at all
            # (row2 is left as it was) and the pivot row is kept: the quotient is unchanged
            # either way, and the final Smith normal form (over ZZ) finishes the job.
            complete = true
            for r2 in collect(colrows[c])
                r2 == r && continue
                row2 = rows[r2]
                empty!(updates)
                fits = true
                for (k, v) in row
                    f, o1 = Base.Checked.mul_with_overflow(row2[c], ε)
                    t, o2 = Base.Checked.mul_with_overflow(f, v)
                    nv, o3 = Base.Checked.sub_with_overflow(get(row2, k, 0), t)
                    if o1 || o2 || o3
                        fits = false
                        break
                    end
                    push!(updates, (k, nv))
                end
                if !fits
                    complete = false
                    continue
                end
                for (k, nv) in updates
                    if nv == 0
                        if haskey(row2, k)
                            delete!(row2, k)
                            delete!(colrows[k], r2)
                        end
                    else
                        if !haskey(row2, k)
                            push!(colrows[k], r2)
                        end
                        row2[k] = nv
                    end
                end
            end
            complete || continue      # generator c is still used by another row: keep the pivot row
            for k in keys(row)
                delete!(colrows[k], r)
            end
            alive[r] = false
            neliminated += 1
            changed = true
        end
    end
    liverows = [rows[r] for r in eachindex(rows) if alive[r] && !isempty(rows[r])]
    cols = sort!(unique!(reduce(vcat, (collect(keys(r)) for r in liverows); init=Int[])))
    ncols_left = ncols - neliminated            # generators not yet eliminated
    if isempty(liverows)
        return AbGroup(ncols_left, Int[]), (0, 0)
    end
    cidx = Dict(c => i for (i, c) in enumerate(cols))
    M = zero_matrix(ZZ, length(liverows), length(cols))
    for (i, row) in enumerate(liverows), (c, v) in row
        M[i, cidx[c]] = ZZ(v)
    end
    S = snf(M)
    diag = [S[i, i] for i in 1:min(size(S)...)]
    nzd = [abs(d) for d in diag if !iszero(d)]
    for d in nzd
        d <= typemax(Int) || error("cokernel_group: invariant factor $d does not fit in Int " *
                                   "(AbGroup stores machine integers); use certify_snf for exact output")
    end
    tors = [Int(d) for d in nzd if d > 1]
    return AbGroup(ncols_left - length(nzd), tors), size(M)
end

