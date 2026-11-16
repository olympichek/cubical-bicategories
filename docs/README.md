# Building the documentation

The site uses Agda’s HTML backend and Pandoc. With the project’s dependencies registered, run these commands from the repository root.

```sh
python3 docs/build.py
python3 -m http.server --bind 127.0.0.1 --directory _build/html 8000
```

Open `http://localhost:8000/`. To use an alternate Agda library registry, pass `--library-file PATH` to the build script.

The documentation uses a Monokai-inspired dark palette. Select **Show justifications** to expand the proof steps in an equational calculation. This preference carries across pages. A direct link to a hidden proof step reveals it.

## Writing a literate page

In a `.lagda.md` file, put an Agda definition or proof in a fenced `agda` block. After that block, explain what the result buys you and why the next step follows. To continue a module or record, start a new block and keep the Agda code at its original indentation. The [bicategory definition](../src/Bicategories/Base.lagda.md) does this inside the record, with the triangle beside its Agda law.

Use LaTeX for mathematical notation in prose, including single variables. Write inline mathematics between single dollar signs, as in `$f : x \to y$`. Use backticks when citing an Agda identifier by name. Put a pair of double dollar signs on lines around a displayed formula or diagram. Pandoc turns this LaTeX into native MathML during the build, so it also renders in the local preview while offline.

## Publishing

On GitHub, select **GitHub Actions** under **Settings → Pages → Source**. CI builds the documentation on pull requests, and successful builds on `main` publish it to [GitHub Pages](https://olympichek.github.io/cubical-bicategories/).
