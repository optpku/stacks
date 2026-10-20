/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projection formulas for fixed-factor derived tensor products

This file records the objectwise projection-formula property for an adjunction between derived
categories.  It uses the canonical fixed-right derived tensor operation and does not assume that
either derived category has been equipped with a second monoidal presentation.
-/

@[expose] public section

open CategoryTheory.MonoidalCategory ComplexShape
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u₁ v₁ w₁ u₂ v₂ w₂

namespace CategoryTheory.Adjunction

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁]
variable [HasDerivedCategory.{w₁} C₁]
variable [MonoidalCategory C₁] [MonoidalPreadditive C₁]
variable [∀ K L : CochainComplex C₁ ℤ,
  HomologicalComplex.HasMapBifunctor K L (curriedTensor C₁) (up ℤ)]
variable [DerivedCategory.DerivedTensor.Right.Has (C := C₁)]

variable {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂]
variable [HasDerivedCategory.{w₂} C₂]
variable [MonoidalCategory C₂] [MonoidalPreadditive C₂]
variable [∀ K L : CochainComplex C₂ ℤ,
  HomologicalComplex.HasMapBifunctor K L (curriedTensor C₂) (up ℤ)]
variable [DerivedCategory.DerivedTensor.Right.Has (C := C₂)]

variable {L : DerivedCategory C₁ ⥤ DerivedCategory C₂}
variable {R : DerivedCategory C₂ ⥤ DerivedCategory C₁}

/-- An adjunction satisfies the fixed-right derived projection formula when
`L.obj X ⊗ᴸ Y` is isomorphic to `L.obj (X ⊗ᴸ R.obj Y)` for every `X` and `Y`.
The class is deliberately Prop-valued: a concrete natural comparison should be supplied by a
monoidal model rather than chosen from an unfinished existence proof. -/
@[stacks 0GL1 "objectwise derived projection formula"]
class DerivedProjectionFormula (adj : L ⊣ R) : Prop where
  /-- The objectwise derived projection-formula isomorphism relation. -/
  isomorphic (X : DerivedCategory C₁) (Y : DerivedCategory C₂) :
    IsIsomorphic (L.obj X ⊗ᴸ Y) (L.obj (X ⊗ᴸ R.obj Y))

end CategoryTheory.Adjunction
