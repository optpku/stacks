/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.Cohomology
import StacksCheckRecall

/-!
@stack 0CQE
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

-- Local instance justification (defeq pin): the chapter writes all derived-category terms in the
-- standard model. This is not a globally canonical typeclass choice.
attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.ModuleCat

variable (A : Type u) [CommRing A]

/- Lemma 15.88.4 (Stacks 0CQE): for a sequential inverse system of derived `A`-modules, the
cohomology of its canonical total right derived inverse limit lies in the Milnor short exact
sequence. This is the `ModuleCat A` specialization of
`CategoryTheory.DerivedLimit.cohomologyShortExact`. -/
@[stacks 0CQE] #check
  (CategoryTheory.DerivedLimit.cohomologyShortExact
    (A := ModuleCat.{u, u} A) :
    (K : DerivedCategory.{u + 1, u, u + 1}
      (SequentialInverseSystem (ModuleCat.{u, u} A))) → (p : ℤ) →
    ∃ (ι : DerivedLimit.R1
        (DerivedLimit.Stage.tower K ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u, u} A) (p - 1)) ⟶
        DerivedLimit.cohomology (C := ModuleCat.{u, u} A) K p)
      (π : DerivedLimit.cohomology (C := ModuleCat.{u, u} A) K p ⟶
          limit (DerivedLimit.Stage.tower K ⋙
            DerivedCategory.homologyFunctor (ModuleCat.{u, u} A) p))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact)

#check @DerivedLimit.R1
#check @IsDerivedLimit.cohomologyShortExact
#check @DerivedLimit.Stage.tower

end CategoryTheory.ModuleCat
