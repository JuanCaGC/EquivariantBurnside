# Exact DCP arrangement data using Julia and OSCAR's GAP interface.
# Input matrices M are the matrices on V^vee, acting on coordinate columns.
# Points of V are rows and act on the right by v -> v*M. Pullback of a
# coordinate f is f(v*M), so its matrix on coordinate columns is M.
# This is the right-action/coordinate-pullback convention in KT_repr Sections
# 6 and 7. In particular eigenvalues, not their inverses, define epsilon.
# A left point representation must first be converted by inverse transpose.
# Subquotient characters use the same positive eigenvalue convention.
# Normal characters are epsilon_1 (affine) or epsilon_1-epsilon (projective),
# followed by successive differences. They are not negated a second time.
# A character coordinate a_j means chi(g_j)=E(d_j)^a_j, with d_j=Order(g_j).
# Cyclic groups use one generator. Others use GAP independent direct factors.
# The actual generators are returned, so all basis choices are reproducible.

module DCP
using Oscar
export arrangement, chains, standard_symmetric, ChainData, Arrangement, all_flags, entry_lookup, entry_action

const GG = GAP.Globals
const loaded = Ref(false)
function initialize!()
    loaded[] && return
    GAP.evalstr(raw"""
DCP_RREF := function(A)
  local B,i,j,k,p,v;
  if Length(A)=0 then return []; fi;
  B:=List(A,ShallowCopy); i:=1;
  for j in [1..Length(B[1])] do
    p:=First([i..Length(B)],k->B[k][j]<>0);
    if p<>fail then
      v:=B[i]; B[i]:=B[p]; B[p]:=v;
      B[i]:=B[i]/B[i][j];
      for k in [1..Length(B)] do
        if k<>i then B[k]:=B[k]-B[k][j]*B[i]; fi;
      od;
      i:=i+1;
      if i>Length(B) then break; fi;
    fi;
  od;
  return B{[1..i-1]};
end;
DCP_Contains := function(B,A)
  return Length(DCP_RREF(Concatenation(B,A)))=Length(B);
end;
DCP_Scalar := function(B,A)
  local T,p,c;
  if Length(B)=0 then return 1; fi;
  T:=B*A; p:=PositionProperty(B[1],x->x<>0);
  c:=T[1][p]/B[1][p];
  if T=c*B then return c; fi;
  return fail;
end;
DCP_QuotientScalar := function(U,W,A)
  local B,v,T,Q,r,s,i;
  B:=ShallowCopy(U); r:=Length(U);
  for v in W do
    if not DCP_Contains(B,[v]) then Add(B,v); fi;
  od;
  s:=Length(B)-r;
  if s=0 then Error("zero quotient"); fi;
  T:=List(B,v->SolutionMat(B,v*A));
  Q:=ExtractSubMatrix(T,[r+1..r+s],[r+1..r+s]);
  if Q=Q[1][1]*IdentityMat(s) then return Q[1][1]; fi;
  return fail;
end;
DCP_Arrangement := function(G,projective)
  local iso,P,els,mats,n,id,C,entries,reps,cl,H,hgens,hclasses,chars,
    chi,B,A,K,vals,h,g,v,p,scalar,N,orb,W,Hp,entry,positions,m;
  iso:=IsomorphismPermGroup(G); P:=Image(iso);
  els:=AsSSortedList(P); mats:=List(els,g->PreImagesRepresentative(iso,g));
  n:=Length(One(G)); id:=IdentityMat(n);
  C:=Subgroup(P,Filtered(els,g->DCP_Scalar(id,mats[Position(els,g)])<>fail));
  entries:=[]; reps:=[];
  for cl in ConjugacyClassesSubgroups(P) do
    H:=Representative(cl);
    if projective and not IsSubgroup(H,C) then continue; fi;
    hgens:=GeneratorsOfGroup(H); hclasses:=ConjugacyClasses(H);
    if projective then chars:=Filtered(Irr(H),c->c[1]=1);
    else chars:=[TrivialCharacter(H)]; fi;
    for chi in chars do
      B:=id;
      for h in hgens do
        p:=PositionProperty(hclasses,c->h in c);
        A:=mats[Position(els,h)]-chi[p]*id;
        K:=NullspaceMat(B*A);
        if Length(K)=0 then B:=[]; else B:=DCP_RREF(K*B); fi;
        if Length(B)=0 then break; fi;
      od;
      if projective and Length(B)=0 then continue; fi;
      scalar:=Filtered(els,function(g)
        local c;
        c:=DCP_Scalar(B,mats[Position(els,g)]);
        if projective then return c<>fail; else return c=1; fi;
      end);
      if Size(H)<>Length(scalar) then continue; fi;
      if ForAny(entries,e->e.basis=B) then continue; fi;
      N:=Subgroup(P,Filtered(els,g->Length(B)=0 or DCP_RREF(B*mats[Position(els,g)])=B));
      positions:=[];
      for g in RightTransversal(P,N) do
        if Length(B)=0 then W:=[]; else W:=DCP_RREF(B*mats[Position(els,g)]); fi;
        Hp:=H^g;
        entry:=rec(group:=PreImage(iso,Hp),permgroup:=Hp,basis:=W,
          dimension:=Length(W),classid:=Length(reps)+1,
          order:=Size(Hp),description:=StructureDescription(Hp));
        entry.charactergenerators:=GeneratorsOfGroup(entry.group);
        entry.charactervalues:=List(entry.charactergenerators,m->DCP_Scalar(W,m));
        Add(entries,entry); Add(positions,Length(entries));
      od;
      Add(reps,positions);
    od;
  od;
  return rec(group:=G,iso:=iso,P:=P,els:=els,mats:=mats,n:=n,
    scalar:=PreImage(iso,C),scalarperm:=C,entries:=entries,orbits:=reps,
    projective:=projective);
end;
DCP_Chain := function(R,indices)
  local es,N,D,ns,ds,g,spaces,i,gen,orders,chars,vals,c,a,normal,
    empty,ngens,dgens,groups;
  es:=R.entries{indices};
  ns:=Filtered(R.els,g->ForAll(es,e->Length(e.basis)=0 or
    DCP_RREF(e.basis*R.mats[Position(R.els,g)])=e.basis));
  N:=Subgroup(R.P,ns);
  spaces:=Concatenation(List(es,e->e.basis),[IdentityMat(R.n)]);
  ds:=Filtered(ns,function(g)
    local M,i;
    if not g in es[1].permgroup then return false; fi;
    M:=R.mats[Position(R.els,g)];
    return ForAll([1..Length(indices)],i->DCP_QuotientScalar(spaces[i],spaces[i+1],M)<>fail);
  end);
  D:=Subgroup(R.P,ds);
  if not IsAbelian(D) then Error("generic stabilizer not abelian"); fi;
  if IsCyclic(D) and Size(D)>1 then gen:=[First(AsSSortedList(D),g->Order(g)=Size(D))];
  elif Size(D)=1 then gen:=[];
  else gen:=IndependentGeneratorsOfAbelianGroup(D); fi;
  orders:=List(gen,Order); chars:=[];
  if R.projective then
    Add(chars,List([1..Length(gen)],i->Position(List([0..orders[i]-1],a->E(orders[i])^a),
      DCP_Scalar(spaces[1],R.mats[Position(R.els,gen[i])]))-1));
  fi;
  for i in [1..Length(indices)] do
    vals:=[];
    for a in [1..Length(gen)] do
      c:=DCP_QuotientScalar(spaces[i],spaces[i+1],R.mats[Position(R.els,gen[a])]);
      Add(vals,Position(List([0..orders[a]-1],i->E(orders[a])^i),c)-1);
    od;
    Add(chars,vals);
  od;
  normal:=[];
  if not R.projective then Add(normal,chars[1]); fi;
  for i in [2..Length(chars)] do
    Add(normal,List([1..Length(orders)],a->(chars[i][a]-chars[i-1][a]) mod orders[a]));
  od;
  return rec(indices:=indices,normalizer:=PreImage(R.iso,N),normalizerorder:=Size(N),
    delta:=PreImage(R.iso,D),deltaperm:=D,deltadescription:=StructureDescription(D),
    deltaorder:=Size(D),generators:=List(gen,g->PreImagesRepresentative(R.iso,g)),
    permgenerators:=gen,orders:=orders,characters:=chars,normalcharacters:=normal);
end;
DCP_Standard := function(n)
  local P,gens,p,M,i,j,v;
  P:=SymmetricGroup(n); gens:=[];
  for p in GeneratorsOfGroup(P) do
    M:=[];
    for i in [1..n-1] do
      v:=List([1..n],j->0); v[i^p]:=1; v[n^p]:=v[n^p]-1;
      Add(M,v{[1..n-1]});
    od;
    Add(gens,M);
  od;
  return Group(gens);
end;
""")
    loaded[] = true
end

struct Arrangement
    raw::GAP.GapObj
    elements::Vector{GAP.GapObj}
    orbit_indices::Vector{Vector{Int}}
    dimension::Int
    projective::Bool
    seconds::Float64
end

struct ChainData
    indices::Vector{Int}
    groups::Vector{GAP.GapObj}
    subspaces::Vector{GAP.GapObj}
    normalizer::GAP.GapObj
    normalizer_order::Int
    delta::GAP.GapObj
    delta_description::String
    delta_order::Int
    basis_generators::Vector{GAP.GapObj}
    basis_orders::Vector{Int}
    characters::Vector{Vector{Int}}
    normal_characters::Vector{Vector{Int}}
    raw::GAP.GapObj
end

gvec(x) = [x[i] for i in 1:Int(GG.Length(x))]
ints(x) = Int.(GAP.gap_to_julia(x))
intvecs(x) = [ints(v) for v in gvec(x)]

"""All affine stabilizers or all projective pairs, including the scalar pair.
The projective formal top infinity is implicit and counted separately.
Subgroups are enumerated up to conjugacy, then their one-dimensional
characters are tested by exact simultaneous eigenspaces and full stabilizers.
This is exhaustive because every actual line stabilizer occurs among these
subgroups and its character occurs among their linear irreducibles.
"""
function arrangement(G::GAP.GapObj; projective=true)
    initialize!()
    t = time()
    r = GG.DCP_Arrangement(G, projective)
    Arrangement(r, gvec(r.entries), intvecs(r.orbits), Int(r.n), projective, time()-t)
end

function chain_data(A, ix)
    r = GG.DCP_Chain(A.raw, GAP.GapObj(ix))
    ChainData(ix, [A.elements[i].group for i in ix],
        [A.elements[i].basis for i in ix], r.normalizer, Int(r.normalizerorder),
        r.delta, String(r.deltadescription), Int(r.deltaorder),
        gvec(r.generators), ints(r.orders), intvecs(r.characters),
        intvecs(r.normalcharacters), r)
end

"""Nonempty chains modulo G. A flag is conjugated as one object.
All contained subspaces are used, not just inclusions among class representatives.
The generic affine stabilizer must fix the initial affine point, hence lies
in Gamma_1. The projective version is scalar on every graded piece.
"""
function chains(A::Arrangement)
    E = A.elements
    eligible = [i for i in eachindex(E) if A.projective ?
        (0 < Int(E[i].dimension) < A.dimension) : Int(E[i].order) > 1]
    contains = Dict(i => [j for j in eligible if Int(E[i].dimension) < Int(E[j].dimension) &&
        Bool(GG.DCP_Contains(E[j].basis, E[i].basis))] for i in eligible)
    flags = Vector{Int}[]
    function extend(ix)
        push!(flags, ix)
        for j in contains[last(ix)]
            extend([ix; j])
        end
    end
    for i in eligible
        extend([i])
    end
    key(B) = String(GG.String(B))
    lookup = Dict(key(e.basis) => i for (i,e) in enumerate(E))
    actions = Vector{Int}[]
    for g in gvec(GG.GeneratorsOfGroup(A.raw.P))
        M = A.raw.mats[Int(GG.Position(A.raw.els,g))]
        push!(actions, [lookup[key(Int(e.dimension)==0 ? e.basis : GG.DCP_RREF(e.basis*M))] for e in E])
    end
    seen = Set{Tuple}()
    result = ChainData[]
    for f in flags
        Tuple(f) in seen && continue
        queue = [f]
        push!(seen, Tuple(f))
        while !isempty(queue)
            q = pop!(queue)
            for a in actions
                z = a[q]
                if !(Tuple(z) in seen)
                    push!(seen, Tuple(z))
                    push!(queue, z)
                end
            end
        end
        push!(result, chain_data(A, f))
    end
    result
end

"""All flags (chains of entries of the arrangement, not modulo G), as lists of indices into `A.elements` ordered by increasing
dimension. These are the lists that `chains` enumerates before taking orbits. A flag contains another flag when the second is a
subsequence of the first."""
function all_flags(A::Arrangement)
    E = A.elements
    eligible = [i for i in eachindex(E) if A.projective ?
        (0 < Int(E[i].dimension) < A.dimension) : Int(E[i].order) > 1]
    contains = Dict(i => [j for j in eligible if Int(E[i].dimension) < Int(E[j].dimension) &&
        Bool(GG.DCP_Contains(E[j].basis, E[i].basis))] for i in eligible)
    flags = Vector{Int}[]
    function extend(ix)
        push!(flags, ix)
        for j in contains[last(ix)]
            extend([ix; j])
        end
    end
    for i in eligible
        extend([i])
    end
    flags
end

"""A dictionary from the row reduced basis (as a string) of every entry to its index, used by `entry_action`."""
entry_lookup(A::Arrangement) = Dict(String(GG.String(e.basis)) => i for (i, e) in enumerate(A.elements))

"""The permutation of the entries of the arrangement induced by the matrix `M` (a point subspace `W` goes to the row space of
`W*M`), as a vector of indices."""
function entry_action(A::Arrangement, lookup, M)
    [lookup[String(GG.String(Int(e.dimension) == 0 ? e.basis : GG.DCP_RREF(e.basis * M)))] for e in A.elements]
end

# The standard basis is e_i-e_n. GAP composes permutations on the right,
# so e_i goes to e_(i^p) and row coordinates become x_(j^(p^-1)).
# The paper writes x_(sigma(j)) using the opposite convention for composing
# named permutations. Relabel sigma as p^-1 when comparing those formulas.
# This is a permutation notation conversion, not a negation of characters.
standard_symmetric(n::Integer) = (initialize!(); GG.DCP_Standard(n))
end
