# LOTAC

LOTAC2 is a modal logic library and textbook written in Lean and Verso.
The original `LOTAC/` development is retained as reference material.

## Build

Build the Lean project and textbook executable:

```sh
lake build
```

Generate the textbook website in `_out/html-multi/`:

```sh
lake exe textbook
```

Preview it locally from the repository root:

```sh
python3 -m http.server 8000 -d _out/html-multi
```

Then open <http://localhost:8000/>.

The book entry point is `LOTAC2.lean`; its chapters live in `LOTAC2/`.
`Textbook/Blocks.lean` provides shared Verso components.
