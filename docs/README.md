# Documentation

Agda typechecks the library and produces highlighted code with links to definitions. Pandoc combines the code with the surrounding prose to build the site. The [site overview](index.md) and the [GitHub README](../README.md) have separate Markdown sources.

## Literate Agda pages

Each `.lagda.md` page follows a construction through its definitions and proofs. Agda reads the fenced `agda` blocks in order. A record or module can span several blocks because the code keeps its indentation across the intervening prose. In the bicategory definition, for example, a diagram shows the two ways to remove an identity arrow just before the `triangle` field says they agree. [Bicategory definition](../src/Bicategories/Base.lagda.md)

Mathematical notation in the prose uses LaTeX, including single variables. Single dollar signs delimit inline expressions such as `$f : x \to y$`. Pairs of double dollar signs delimit displayed equations and diagrams. Pandoc renders both as MathML at build time, so formulas also display offline. Backticks mark literal Agda names such as `triangle`.

The highlighted code uses a Monokai-inspired dark theme. In an equational calculation, each justification appears between the angle brackets of its step.

## Local preview

From the repository root, the first command builds the site in `_build/html`. The second serves the result at `http://localhost:8000/`.

```sh
python3 docs/build.py
python3 -m http.server --bind 127.0.0.1 --directory _build/html 8000
```

The build uses the libraries registered with Agda. The optional `--library-file PATH` argument selects a different registry.

## GitHub Pages

GitHub Actions builds the documentation on pull requests and publishes successful builds from `main` to [GitHub Pages](https://olympichek.github.io/cubical-bicategories/).

CI caches Agda’s checked modules for the project, the Cubical library, and Agda’s builtins. With a warm cache, edits to the README, site overview, or theme regenerate the site using the existing checks. An edit to prose inside a `.lagda.md` file changes the Agda source for that module. Agda rechecks it and its dependents so links in the highlighted proofs still point to the right places.
