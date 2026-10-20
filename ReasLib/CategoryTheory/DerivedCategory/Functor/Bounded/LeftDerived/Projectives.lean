/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.LeftDerived.Canonical
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.KProjective.Bounded.Global
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor.KProjective.Bounded

noncomputable section

universe w vA vB uA uB

namespace CategoryTheory.Functor.LeftDerived.Bounded

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  (F : A ⥤ B) [F.Additive] [EnoughProjectives A]

/-- Enough projectives provide the pointwise data required for the bounded-above left-derived
functor construction. -/
@[stacks 03T7]
noncomputable instance hasDerivedOfEnoughProjectives :
    F.toBoundedAboveDerived.HasLeftDerivedFunctor
      (HomotopyCategory.Minus.quasiIso A) := by
  have resolutions (complex : CochainComplex.Minus A) :
      Nonempty (CochainComplex.ProjectiveResolution complex.obj) := by
    obtain ⟨bound, boundInstance⟩ := complex.property
    obtain ⟨resolution, resolutionBound, termwiseEpi⟩ :=
      CochainComplex.ProjectiveResolution.exists_strictlyLE_with_termwise_epi
        bound boundInstance
    exact ⟨resolution⟩
  have pointwise := hasPointwiseOfResolutions
    F.toBoundedAboveDerived resolutions
  exact F.toBoundedAboveDerived.hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor
    (HomotopyCategory.Minus.quasiIso A)

/-- The bounded-above left-derived counit is invertible on projective complexes. -/
@[stacks 03T7]
theorem counit_isIso_on_projectives
    (X : HomotopyCategory.Minus.TermsIn A (isProjective A)) :
    IsIso ((counit F).app
      ((HomotopyCategory.Minus.TermsIn.ι A).obj X)) := by
  sorry

end CategoryTheory.Functor.LeftDerived.Bounded

end
