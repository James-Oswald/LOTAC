# LOTAC

LOTAC is a modal logic library and textbook written in Lean and Verso.

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

The book entry point is `Textbook.lean`; chapters live in `Textbook/`.
