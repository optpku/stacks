/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Functorial computations for homological complexes

This leaf records the structural computations for the functor induced on homological complexes by
a zero-morphism-preserving functor.  It is independent of a particular complex shape or
application such as filtrations.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe vC vD uC uD uI

namespace CategoryTheory.Functor

variable {I : Type uI} {C : Type uC} {D : Type uD}
  [Category.{vC} C] [Category.{vD} D]
  [HasZeroMorphisms C] [HasZeroMorphisms D]

/-- Applying a zero-morphism-preserving functor to a complex commutes with its canonical
degree-indexed short complex. -/
@[simp]
theorem mapHomologicalComplex_obj_sc (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (c : ComplexShape I) (K : HomologicalComplex C c) (i : I) :
    ((F.mapHomologicalComplex c).obj K).sc i = (K.sc i).map F := sorry

end CategoryTheory.Functor
