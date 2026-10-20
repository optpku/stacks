/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Localization.Adjunction
public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory
import Mathlib.Tactic.CrossRefAttribute

/-!
# Exact adjunctions on derived categories

An adjunction between exact functors on abelian categories descends to the corresponding
derived categories.  The construction uses the canonical localization squares supplied by
`Functor.mapDerivedCategoryFactors`; no additional absolute-derived hypotheses are needed.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape

noncomputable section

universe u₁ v₁ w₁ u₂ v₂ w₂

namespace CategoryTheory.Functor.MapDerivedCategory

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁]
variable [HasDerivedCategory.{w₁} C₁]
variable {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂]
variable [HasDerivedCategory.{w₂} C₂]
variable (F : C₁ ⥤ C₂)
variable [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The canonical 2-commutative square expressing that `F.mapDerivedCategory` is induced by
the termwise action of the exact functor `F` on cochain complexes. -/
@[stacks 08FJ "exact functor localization square", implicit_reducible]
noncomputable instance catCommSq :
    CatCommSq (F.mapHomologicalComplex (up ℤ)) DerivedCategory.Q
      DerivedCategory.Q F.mapDerivedCategory where
  iso := F.mapDerivedCategoryFactors.symm

end CategoryTheory.Functor.MapDerivedCategory

namespace CategoryTheory.Adjunction

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁]
variable [HasDerivedCategory.{w₁} C₁]
variable {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂]
variable [HasDerivedCategory.{w₂} C₂]
variable {L : C₁ ⥤ C₂} {R : C₂ ⥤ C₁}
variable [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
variable [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]

/-- The adjunction on derived categories induced by an adjunction between exact functors. -/
@[stacks 08FJ "exact adjunction on derived categories"]
noncomputable def mapDerivedCategory (adj : L ⊣ R) :
    L.mapDerivedCategory ⊣ R.mapDerivedCategory :=
  (Adjunction.mapHomologicalComplexAdjunction adj (up ℤ)).localization
    DerivedCategory.Q
    (HomologicalComplex.quasiIso C₁ (up ℤ))
    DerivedCategory.Q
    (HomologicalComplex.quasiIso C₂ (up ℤ))
    L.mapDerivedCategory R.mapDerivedCategory

end CategoryTheory.Adjunction

-- Any `sorryAx` below is inherited from the triangle-law fields of
-- `Adjunction.mapHomologicalComplexAdjunction`; the localization squares and functors are
-- concrete.
