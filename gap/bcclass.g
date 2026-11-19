# bcclass.g -- locate a symbol (H,Y,beta) of SC_n(G) inside the Theorem 5.2 decomposition
#   BC_n(G) = (+)_{[H,Y]} B_n(H)/(C_(H,Y))
# using the same class representatives and the same coordinates as BCStructure in ../bc_structure.g.
#
# BCBuild(G)  stores, in the global BCB, one record per G-class of nontrivial abelian H, with
#             H (representative), gens (independent generators), d (their orders), N = N_G(H),
#             pairs = one record per N-orbit of Y between H and C_G(H): orb (the orbit) and
#             mats (the action of N_G(H) n N_G(Y) on H, as in BCStructure).
# BCLocate(G, hgens, ygens) finds the block (b, p) and an element conj with
#             H^conj = BCB[b].H and Y^conj = the representative of orbit p.
# BCExpsMat(b, conj, hgens, ords) returns the matrix F with F[i][j] = exponent of the given generator h_j
#             in the preimage (under x -> x^conj) of the i-th independent generator of BCB[b].H.

BCB := [];;

BCBuild := function(G)
  local cl, H, gens, d, C, N, Ys, inter, orbs, pairs, o, Y, S, mats, g, M;
  BCB := [];
  for cl in ConjugacyClassesSubgroups(G) do
    H := Representative(cl);
    if Size(H) > 1 and IsAbelian(H) then
      gens := IndependentGeneratorsOfAbelianGroup(H);
      d    := List(gens, Order);
      C    := Centralizer(G, H);
      N    := Normalizer(G, H);
      if Size(C) = Size(H) then
        Ys := [H];
      else
        inter := IntermediateSubgroups(C, H);
        Ys := Concatenation([H], inter.subgroups, [C]);
      fi;
      orbs  := Orbits(N, Ys, OnPoints);
      pairs := [];
      for o in orbs do
        Y := o[1];
        S := Normalizer(N, Y);
        mats := [];
        for g in SmallGeneratingSet(S) do
          M := List(gens, x -> IndependentGeneratorExponents(H, x^g));
          if M <> IdentityMat(Length(d)) then Add(mats, M); fi;
        od;
        Add(pairs, rec(orb := o, mats := mats, Ysize := Size(Y)));
      od;
      Add(BCB, rec(H := H, gens := gens, d := d, N := N, pairs := pairs));
    fi;
  od;
  return Length(BCB);
end;;

BCInfo := function(b)
  local blk;
  blk := BCB[b];
  return rec(d := blk.d, mats := List(blk.pairs, p -> p.mats), ysizes := List(blk.pairs, p -> p.Ysize));
end;;

BCLocate := function(G, hgens, ygens)
  local H, Y, i, blk, g, Y1, j, nn;
  H := Subgroup(G, hgens);
  Y := ClosureGroup(Subgroup(G, ygens), H);
  for i in [1 .. Length(BCB)] do
    blk := BCB[i];
    if Size(blk.H) = Size(H) then
      g := RepresentativeAction(G, H, blk.H, OnPoints);
      if g <> fail then
        Y1 := Y^g;
        for j in [1 .. Length(blk.pairs)] do
          if Y1 in blk.pairs[j].orb then
            nn := RepresentativeAction(blk.N, Y1, blk.pairs[j].orb[1], OnPoints);
            return rec(b := i, p := j, conj := g * nn);
          fi;
        od;
      fi;
    fi;
  od;
  return fail;
end;;

BCExps := function(hgens, ords, u)
  local t, x, j;
  for t in Cartesian(List(ords, o -> [0 .. o - 1])) do
    x := One(u);
    for j in [1 .. Length(t)] do x := x * hgens[j]^t[j]; od;
    if x = u then return t; fi;
  od;
  return fail;
end;;

BCExpsMat := function(b, conj, hgens, ords)
  return List(BCB[b].gens, g -> BCExps(hgens, ords, g^(conj^-1)));
end;;

# BCBlockInfo(b, p) returns the data that names the block (b, p) and lets a certificate
# rebuild it: descriptions, sizes, the independent generators of the representative H and
# generators of the representative Y (as GAP strings, evaluable for permutation and matrix groups).
BCBlockInfo := function(b, p)
  local blk, pr, Y, ydesc;
  blk := BCB[b];
  pr := blk.pairs[p];
  Y := pr.orb[1];
  if Size(Y) <= 2000 then ydesc := StructureDescription(Y);
  else ydesc := Concatenation("order ", String(Size(Y))); fi;
  return rec(d := blk.d, Hdesc := StructureDescription(blk.H), Ydesc := ydesc,
             Hgens := List(blk.gens, String), Ygens := List(GeneratorsOfGroup(Y), String),
             Ysize := Size(Y), orbitsize := Length(pr.orb));
end;;

BCNumBlocks := function()
  return List(BCB, blk -> Length(blk.pairs));
end;;
