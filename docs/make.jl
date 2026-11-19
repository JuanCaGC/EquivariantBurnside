using Documenter, EquivariantBurnside, Oscar

DocMeta.setdocmeta!(EquivariantBurnside, :DocTestSetup,
    :(using EquivariantBurnside, Oscar), recursive = true)

makedocs(
    modules = [EquivariantBurnside],
    sitename = "EquivariantBurnside",
    doctest = true,
    warnonly = false,
    checkdocs = :exports,
    remotes = nothing,
    format = Documenter.HTML(prettyurls = false, edit_link = nothing, repolink = nothing),
    pages = ["Home" => "index.md", "API reference" => "api.md",
             "Conventions" => "conventions.md", "Performance baseline" => "benchmarks.md"],
)
