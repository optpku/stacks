/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Cochain functors valued in a derived category

This file owns the variance-neutral construction obtained by applying an additive functor
termwise to cochain complexes and then localizing the target. Left- and right-derived APIs build
their universal properties on this common datum.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe uA vA uB vB wB

namespace CategoryTheory.Functor.Derived.Cochain

variable {A : Type uA} {B : Type uB}
variable [Category.{vA} A] [Preadditive A]
variable [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]

/-- Apply an additive functor termwise to cochain complexes, then localize the target. -/
@[stacks 05TH "cochain-level derived localization"]
abbrev toDerived (F : A ⥤ B) [F.Additive] :
    CochainComplex A ℤ ⥤ DerivedCategory B :=
  F.mapHomologicalComplex (up ℤ) ⋙
    (DerivedCategory.Q : CochainComplex B ℤ ⥤ DerivedCategory B)

/-- Objectwise form of cochain-level derived localization. -/
@[stacks 05TH "cochain-level derived localization on objects"]
theorem toDerived_obj (F : A ⥤ B) [F.Additive] (K : CochainComplex A ℤ) :
    (toDerived F).obj K =
      (DerivedCategory.Q : CochainComplex B ℤ ⥤ DerivedCategory B).obj
        ((F.mapHomologicalComplex (up ℤ)).obj K) := sorry

/-- Morphismwise form of cochain-level derived localization. -/
@[stacks 05TH "cochain-level derived localization on morphisms"]
theorem toDerived_map (F : A ⥤ B) [F.Additive]
    {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    (toDerived F).map f =
      (DerivedCategory.Q : CochainComplex B ℤ ⥤ DerivedCategory B).map
        ((F.mapHomologicalComplex (up ℤ)).map f) := sorry



end CategoryTheory.Functor.Derived.Cochain
