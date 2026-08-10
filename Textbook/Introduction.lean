import VersoManual
import LOTAC.Formula

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Introduction" =>

Modal formulas are built from atoms, falsity, implication, and the box operator.
The remaining connectives are defined from these primitives.

For example, here are an atom and the modal formula that asserts its necessity:

```lean
def p : L := L.atom 0
def necessarilyP : L := □ₜp
```

Because the examples are elaborated as part of the textbook, changes to the LOTAC library that
invalidate them also cause the textbook build to fail.
