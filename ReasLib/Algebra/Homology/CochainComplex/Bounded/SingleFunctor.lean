/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import Mathlib.CategoryTheory.Shift.SingleFunctorsLift
import Mathlib.Tactic.CrossRefAttribute

/-!
# Single Objects in Bounded-Below Cochain Complexes

This file lifts the shift-compatible family of single-object cochain complexes to the
full subcategory of bounded-below complexes.  It also records the canonical comparisons
with the ambient cochain-complex and bounded-below homotopy-category models.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe v u

namespace CochainComplex.Plus

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasZeroObject C]

/-- A cochain complex concentrated in degree `n` is bounded below. -/
@[stacks 015A "single cochain complexes are bounded below"]
theorem single_obj_mem (n : ℤ) (X : C) :
    CochainComplex.plus C ((CochainComplex.singleFunctor C n).obj X) := sorry

/-- The shift-compatible family of single-object functors into bounded-below cochain
complexes. -/
@[stacks 015A "single functors into bounded-below cochain complexes"]
noncomputable def singleFunctors : SingleFunctors C (CochainComplex.Plus C) ℤ :=
  SingleFunctors.lift (CochainComplex.singleFunctors C) (CochainComplex.Plus.ι C)
    (fun n ↦ (CochainComplex.plus C).lift
      (CochainComplex.singleFunctor C n) (single_obj_mem C n))
    (fun _ ↦ Iso.refl _)

/-- The functor sending an object to the bounded-below cochain complex concentrated in
degree `n`. -/
@[stacks 015A "single functor into bounded-below cochain complexes"]
noncomputable abbrev singleFunctor (n : ℤ) : C ⥤ CochainComplex.Plus C :=
  (singleFunctors C).functor n

/-- Forgetting bounded-below support recovers the ambient cochain single-object functor. -/
@[stacks 015A "underlying single cochain complex"]
noncomputable def singleFunctorCompιIso (n : ℤ) :
    singleFunctor C n ⋙ CochainComplex.Plus.ι C ≅
      CochainComplex.singleFunctor C n :=
  Iso.refl _

/-- The bounded-below single-object functor is additive. -/
instance singleFunctor.additive (n : ℤ) : (singleFunctor C n).Additive := sorry

section Homotopy

variable [HasBinaryBiproducts C]

/-- Passing a bounded-below single complex to the homotopy category gives the canonical
bounded-below homotopy single object. -/
@[stacks 015A "single complex under the bounded-below homotopy quotient"]
noncomputable def singleFunctorCompQuotientIso (n : ℤ) :
    singleFunctor C n ⋙ HomotopyCategory.Plus.quotient C ≅
      HomotopyCategory.Plus.singleFunctor C n :=
  Iso.refl _

end Homotopy

end CochainComplex.Plus
