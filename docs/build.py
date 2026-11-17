"""Build the navigable Agda documentation in _build/html."""

import argparse
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
DOCS = ROOT / "docs"


def project_modules():
    modules = {}
    for extension in (".lagda.md", ".agda"):
        for path in (ROOT / "src").rglob(f"*{extension}"):
            relative = path.relative_to(ROOT / "src").as_posix()
            name = relative.removesuffix(extension).replace("/", ".")
            modules[name] = path.relative_to(ROOT)
    return modules


def render(markdown, title, output, source=None):
    command = [
        "pandoc", f"--defaults={DOCS / 'pandoc.yaml'}",
        f"--template={DOCS / 'page.html'}", "--css=Agda.css", "--css=reading.css",
        "--metadata", f"pagetitle={title}", "--output", str(output),
    ]
    env = os.environ.copy()
    if source is not None:
        env["AGDA_DOC_SOURCE"] = source.as_posix()
        command.append(f"--lua-filter={DOCS / 'source-links.lua'}")
    subprocess.run(command, input=markdown, text=True, encoding="utf-8", cwd=ROOT, env=env, check=True)


def module_index(modules):
    groups = {}
    for name in sorted(modules):
        parts = name.split(".")
        group = parts[1] if len(parts) > 2 else "Foundations"
        groups.setdefault(group, []).append(name)
    lines = ["# Module index", ""]
    for group in sorted(groups, key=lambda g: (g != "Foundations", g)):
        lines.extend([f"## {group}", ""])
        lines.extend(f"- [`{name}`]({name}.html)" for name in groups[group])
        lines.append("")
    return "\n".join(lines)


def build(library_file):
    for tool in ("agda", "pandoc"):
        if shutil.which(tool) is None:
            raise SystemExit(f"Install {tool} and make it available on PATH to build the documentation.")
    build_dir = ROOT / "_build"
    build_dir.mkdir(exist_ok=True)
    destination = build_dir / "html"
    modules = project_modules()
    with tempfile.TemporaryDirectory(dir=build_dir, prefix="docs-") as temporary:
        work = Path(temporary)
        highlighted = work / "highlighted"
        args = ["agda", "-Werror", "--html", "--html-highlight=code", f"--html-dir={highlighted}"]
        if library_file:
            args.append(f"--library-file={library_file}")
        subprocess.run([*args, "src/Bicategories/Everything.agda"], cwd=ROOT, check=True)

        site = work / "site"
        site.mkdir()
        shutil.copyfile(highlighted / "Agda.css", site / "Agda.css")
        shutil.copyfile(ROOT / "LICENSE", site / "project-license.txt")
        for asset in ("reading.css", "reasoning.js", "dependency-licenses.txt"):
            shutil.copyfile(DOCS / asset, site / asset)

        for path in sorted(highlighted.iterdir()):
            if path.suffix not in {".md", ".html"}:
                continue
            name = path.stem
            content = path.read_text(encoding="utf-8")
            if path.suffix == ".html":
                # With code-only highlighting, ordinary Agda modules are HTML fragments.
                content = f'# `{name}`\n\n<pre class="Agda">{content}</pre>\n'
            # Agda keeps blank lines before a literate fence inside the highlighted block.
            content = re.sub(r"\n[ \t\n]+</pre>", "\n</pre>", content)
            render(content, name, site / f"{name}.html", modules.get(name))

        for name in modules:
            if not (site / f"{name}.html").is_file():
                raise SystemExit(f"Missing documentation for {name}; check Bicategories.Everything imports.")
        index = DOCS / "index.md"
        render(index.read_text(encoding="utf-8"), "Cubical Bicategories",
               site / "index.html", index.relative_to(ROOT))
        render(module_index(modules), "Module index", site / "modules.html")

        # Only replace the previous preview after all pages render successfully.
        if destination.exists():
            destination.rename(work / "previous")
        try:
            site.rename(destination)
        except OSError:
            if (work / "previous").exists():
                (work / "previous").rename(destination)
            raise
    print(f"Generated documentation for {len(modules)} project modules: {destination / 'index.html'}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--library-file", type=Path, help="use an alternate Agda library registry")
    options = parser.parse_args()
    build(options.library_file.resolve() if options.library_file else None)
