/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.CochainComplex.KInjective.Resolution
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.Tower

@[expose] public section

/-!
# K-Injective Resolution Criterion for the Stagewise Tower

This module records the generic essential-surjectivity criterion in terms of
K-injective resolutions. Concrete sources of resolutions belong in leaves.
@stack 08U5
@stack 0CQ9
@stack 0CQD
-/

open CategoryTheory.Limits

universe wA wSys u v

namespace CategoryTheory.DerivedLimit.Stage.TowerFunctor

variable {A : Type u} [Category.{v} A] [Abelian A]
variable [HasDerivedCategory.{wA} A]
variable [HasDerivedCategory.{wSys} (SequentialInverseSystem A)]

/-- Lemma 15.87.11 (0CQ9), in resolution form: the stagewise tower functor is essentially
surjective when every cochain complex admits a K-injective resolution. -/
@[stacks 0CQ9, stacks 0CQD, stacks 08U5]
theorem essSurj_of_resolution
    (h_resolution :
      ∀ K : CochainComplex A ℤ, Nonempty (CochainComplex.KInjectiveResolution K)) :
    (DerivedLimit.Stage.towerFunctor A).EssSurj := sorry

end CategoryTheory.DerivedLimit.Stage.TowerFunctor
