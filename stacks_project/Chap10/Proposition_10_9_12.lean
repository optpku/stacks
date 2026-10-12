/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Exact
import StacksCheckRecall

@[expose] public section

/-!
# Proposition 10.9.12

@stack 00CS
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Proposition 10.9.12: if `L ⟶ M ⟶ N` is an exact sequence of `R`-modules, then the induced
sequence `LocalizedModule S L ⟶ LocalizedModule S M ⟶ LocalizedModule S N` is exact. This is
exactly the canonical theorem `LocalizedModule.map_exact`. -/
@[stacks 00CS]
#check @LocalizedModule.map_exact
