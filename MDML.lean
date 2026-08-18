import VersoManual
import Textbook.Bibliography
import MDML.PML

open Verso.Genre Manual
open Textbook
open Textbook.Bibliography
open scoped Verso.Doc.Concrete

def MDML := verso (Manual) "Many Dimensional Modal Logics In Lean"
:::::::

%%%
authors := ["James Oswald"]
%%%

MDML is a textbook about modal logic whose definitions, examples,
and proofs are checked by Lean. The book is named after the famous modal logic
textbook "Many Dimensional Modal Logics : Theory and Applications"
{cite Gabbay2003b}[]. The book also pulls heavily from Goldblatt's
"Logics of Time and Computation"{cite Goldblatt1992}[].


{include 1 MDML.PML}
:::::::

def main := manualMain MDML.toPart
