/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat functors on slice categories

This leaf records stability of representable flatness under the functor between
over categories induced by an arbitrary functor.  It has no site-topology
dependency.
-/

@[expose] public section

universe uC vC uD vD

namespace CategoryTheory

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]

/-- Lemma 7.28.1: representable flatness is stable under the functor on slice
categories induced by a functor. -/
@[stacks 03CF]
theorem RepresentablyFlat.overPost
    (u : C ⥤ D) [RepresentablyFlat u] (U : C) :
    RepresentablyFlat (Over.post (X := U) u) := sorry

end CategoryTheory
