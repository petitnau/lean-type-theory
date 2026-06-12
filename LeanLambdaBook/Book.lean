import VersoManual
import LeanLambda.L0
import LeanLambda.L1
import LeanLambda.L2

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Lambda Calculus in Lean" =>

This book develops lambda calculi as object languages inside Lean.
The chapters below are the actual Lean source files rendered as literate
pages.  The book is therefore a table of contents and publishing layer for the
course files, not a second copy of their content.

{includeLiterate "." LeanLambda.L0 "L0: De Bruijn Terms" (level := 1)}

{includeLiterate "." LeanLambda.L1 "L1: Named Terms" (level := 1)}

{includeLiterate "." LeanLambda.L2 "L2: Simple Types" (level := 1)}

# Building
%%%
tag := "building"
%%%

The book target writes a static multi-page HTML site.

```
lake exe generate-book --output _out/book
```

The generated site lives in `_out/book/html-multi`.
