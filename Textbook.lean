import VersoManual
import Textbook.Introduction
import LOTAC.Formula

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "LOTAC" =>

%%%
authors := ["James"]
%%%

LOTAC is a textbook about modal logic whose definitions, examples, and proofs are checked by Lean.

{include 1 Textbook.Introduction}

{include 1 LOTAC.Formula}
