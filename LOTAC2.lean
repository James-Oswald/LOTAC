import VersoManual
import Textbook.Bibliography
import LOTAC2.Formula
import LOTAC2.Models

open Verso.Genre Manual
open Textbook
open Textbook.Bibliography

#doc (Manual) "Many Dimensional Modal Logics In Lean" =>

%%%
authors := ["James Oswald"]
%%%

LOTAC is a textbook about modal logic whose definitions, examples,
and proofs are checked by Lean. The book is named after the famous modal logic
textbook "Many Dimensional Modal Logics : Theory and Applications"
{cite Gabbay2003b}[]. The book also pulls heavily from Goldblatt's
"Logics of Time and Computation"{cite Goldblatt1992}[].


{include 1 LOTAC2.Formula}

{include 1 LOTAC2.Models}
