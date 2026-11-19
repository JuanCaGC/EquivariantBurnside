# One isolated measurement. Standard output is a single tab-separated record.
# Package diagnostics go to standard error and are retained by the driver.
redirect_stdout(stderr) do
    @eval using EquivariantBurnside, Oscar
end

function make_group(name)
    startswith(name, "S_") && return symmetric_group(parse(Int, name[3:end]))
    startswith(name, "D_") && return dihedral_group(PermGroup, 2parse(Int, name[3:end]))
    if startswith(name, "He_")
        p = parse(Int, name[4:end])
        return GAP.evalstr("Image(IsomorphismPermGroup(ExtraspecialGroup($(p^3), \"+\")))")
    end
    name == "C_8^2:C_3" || error("unknown group")
    # Copied from support/ex75.jl, including its relation check.
    return GAP.evalstr("""
    (function()
      local pt, a, b, m, mi;
      pt := function(i,j) return 8*(i mod 8)+(j mod 8)+1; end;
      a := PermList(List([0..63], k -> pt(QuoInt(k,8)+1, k mod 8)));
      b := PermList(List([0..63], k -> pt(QuoInt(k,8), (k mod 8)+1)));
      m := PermList(List([0..63], k -> pt(k mod 8, -QuoInt(k,8)-(k mod 8))));
      mi := m^-1;
      if m*a*m^-1 = b^-1 and m*b*m^-1 = a*b^-1 then return Group(a,b,m);
      elif mi*a*mi^-1 = b^-1 and mi*b*mi^-1 = a*b^-1 then return Group(a,b,mi);
      else Error("could not realize the relations"); fi;
    end)()
    """)
end

function measure(name, n, route)
    route in ("oscar", "gap", "tom") || error("unknown route")
    warm_group = symmetric_group(4)
    warm = route == "tom" ? bc_structure_tom(4) :
           route == "gap" ? bc_structure_gap(warm_group) : bc_structure(warm_group)
    bc(warm, n)
    G = make_group(name)
    G isa GAP.GapObj && (G = Oscar._oscar_group(G))
    G isa PermGroup || error("expected an OSCAR permutation group")
    GC.gc()
    structure = @timed (route == "tom" ? bc_structure_tom(parse(Int, name[3:end])) :
                        route == "gap" ? bc_structure_gap(G) : bc_structure(G))
    result = @timed bc(structure.value, n)
    peak = Sys.maxrss()
    return ["ok", string(structure.time), string(result.time),
            string(structure.bytes + result.bytes), string(peak),
            string(result.value.total), string(npairs(structure.value)),
            string(structure.value.order), "", string(VERSION),
            string(pkgversion(Oscar)), String(GAP.Globals.GAPInfo.Version)]
end

clean(x) = replace(string(x), '\t' => ' ', '\n' => ' ', '\r' => ' ')
function main()
    name, ns, route = ARGS
    row = try
        redirect_stdout(stderr) do
            measure(name, parse(Int, ns), route)
        end
    catch e
        msg = sprint(showerror, e)
        status = e isa OutOfMemoryError ? "oom" :
                 occursin(r"unavailable|no TomLib table", msg) ? "unavailable" : "error"
        [status, "", "", "", string(Sys.maxrss()), "", "", "", msg,
         string(VERSION), string(pkgversion(Oscar)), String(GAP.Globals.GAPInfo.Version)]
    end
    println(join(clean.(row), '\t'))
end
main()
