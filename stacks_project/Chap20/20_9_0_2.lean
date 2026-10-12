/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Cech.Refinement
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace

/-!
The indexed-open refinement predicate and its formal-coproduct morphism are coefficient-free Čech
infrastructure.  Their reusable owner is
`ReasLib.CategoryTheory.Sites.Cech.Refinement`; this chapter file is a recall bridge only.
-/

/- The refinement data are used by the tagged total-Čech map in item 20.25.0.2 (08BM). -/
@[stacks 08BM "indexed-open refinement predicate"]
#check @CategoryTheory.IsRefinement

@[stacks 08BM "formal-coproduct refinement morphism"]
#check @CategoryTheory.refinementHom

#print axioms CategoryTheory.IsRefinement
#print axioms CategoryTheory.refinementHom

