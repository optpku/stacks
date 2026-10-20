/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.FlatRepresentative

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v w r

namespace CategoryTheory.Sheaf.ModuleDerived

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (Λ : Type w) [CommRing Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]

/-- Restriction of module sheaves to a slice site preserves addition of morphisms. -/
instance overPullbackAdditive (U : C)
    [Preadditive (Sheaf J (ModuleCat.{w} Λ))]
    [Preadditive (Sheaf (J.over U) (ModuleCat.{w} Λ))] :
    (J.overPullback (ModuleCat.{w} Λ) U).Additive := sorry

/-- Restriction of module sheaves to a slice site preserves finite limits. -/
instance overPullbackPreservesFiniteLimits (U : C) :
    PreservesFiniteLimits (J.overPullback (ModuleCat.{w} Λ) U) := sorry

/-- Restriction of module sheaves to a slice site preserves finite colimits. -/
instance overPullbackPreservesFiniteColimits (U : C) :
    PreservesFiniteColimits (J.overPullback (ModuleCat.{w} Λ) U) := sorry

variable [Abelian (Sheaf J (ModuleCat.{w} Λ))]
variable [∀ U : C, Abelian (Sheaf (J.over U) (ModuleCat.{w} Λ))]
variable [HasDerivedCategory.{r} (Sheaf J (ModuleCat.{w} Λ))]
variable [∀ U : C, HasDerivedCategory.{r} (Sheaf (J.over U) (ModuleCat.{w} Λ))]

/-- The derived restriction functor from module sheaves on a site to module sheaves on a
slice site, induced by exact restriction of sheaves. -/
def overPullback (U : C) :
    DerivedCategory (Sheaf J (ModuleCat.{w} Λ)) ⥤
      DerivedCategory (Sheaf (J.over U) (ModuleCat.{w} Λ)) :=
  (J.overPullback (ModuleCat.{w} Λ) U).mapDerivedCategory

variable [∀ U : C, ((J.over U).W (A := ModuleCat.{w} Λ)).IsMonoidal]

/-- A derived module sheaf has locally finite Tor dimension if every site object admits a
covering on whose members its restriction has a bounded termwise-flat representative.
The finite interval may depend on the covering member. -/
def locallyFiniteTorDimension : ObjectProperty (DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) :=
  fun E ↦ ∀ U : C, ∃ cover : J.Cover U, ∀ member : cover.Arrow,
    ∃ a b : ℤ, a ≤ b ∧
      DerivedCategory.HasFlatRepresentativeIn ((overPullback J Λ member.Y).obj E) a b

/-- Locally finite Tor dimension is equivalent to the covering-local bounded-flat-
representative criterion, with a separate finite interval on each covering member. -/
theorem locallyFiniteTorDimension_iff (E : DerivedCategory (Sheaf J (ModuleCat.{w} Λ))) :
    locallyFiniteTorDimension J Λ E ↔
      ∀ U : C, ∃ cover : J.Cover U, ∀ member : cover.Arrow,
        ∃ a b : ℤ, a ≤ b ∧
          DerivedCategory.HasFlatRepresentativeIn ((overPullback J Λ member.Y).obj E) a b := sorry

end CategoryTheory.Sheaf.ModuleDerived
