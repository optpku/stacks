/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.LocallyConstant.Derived.ChainMap
import Mathlib.Tactic.CrossRefAttribute

/-!
# Local descent of morphisms between constant derived sheaves

This leaf separates the one-slice lifting predicate from its cover-wise form, then records the
perfect-source theorem used by the locally constant derived tensor arguments.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v w

namespace CategoryTheory.Sheaf.DerivedRestriction

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Λ : Type w} [Ring Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]
variable [Abelian (Sheaf J (ModuleCat.{w} Λ))]
variable [∀ U : C, Abelian (Sheaf (J.over U) (ModuleCat.{w} Λ))]
variable [HasDerivedCategory (Sheaf J (ModuleCat.{w} Λ))]
variable [∀ U : C, HasDerivedCategory (Sheaf (J.over U) (ModuleCat.{w} Λ))]
variable [J.WEqualsLocallyBijective (ModuleCat.{w} Λ)]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective (ModuleCat.{w} Λ)]
variable [(constantSheaf J (ModuleCat.{w} Λ)).Additive]
variable [PreservesFiniteLimits (constantSheaf J (ModuleCat.{w} Λ))]
variable [PreservesFiniteColimits (constantSheaf J (ModuleCat.{w} Λ))]
variable [∀ U : C, (constantSheaf (J.over U) (ModuleCat.{w} Λ)).Additive]
variable [∀ U : C, PreservesFiniteLimits (constantSheaf (J.over U) (ModuleCat.{w} Λ))]
variable [∀ U : C, PreservesFiniteColimits (constantSheaf (J.over U) (ModuleCat.{w} Λ))]
variable [∀ U : C, (J.overPullback (ModuleCat.{w} Λ) U).Additive]
variable [∀ U : C, PreservesFiniteLimits (J.overPullback (ModuleCat.{w} Λ) U)]
variable [∀ U : C, PreservesFiniteColimits (J.overPullback (ModuleCat.{w} Λ) U)]

/-- A morphism between constant derived sheaves is induced on `U` when, after the canonical
restriction comparison, it is the constant-sheaf image of a coefficient-side derived morphism. -/
@[stacks 09BE "induced by a constant derived morphism on one slice"]
def IsInducedOn {K L : DerivedCategory (ModuleCat.{w} Λ)}
    (φ : (constantSheaf J (ModuleCat.{w} Λ)).mapDerivedCategory.obj K ⟶
      (constantSheaf J (ModuleCat.{w} Λ)).mapDerivedCategory.obj L)
    (U : C) : Prop :=
  ∃ α : K ⟶ L,
    CommSq
      (((J.overPullback (ModuleCat.{w} Λ) U).mapDerivedCategory).map φ)
      ((constantSheafOverDerivedIso U).hom.app K)
      ((constantSheafOverDerivedIso U).hom.app L)
      (((constantSheaf (J.over U) (ModuleCat.{w} Λ)).mapDerivedCategory).map α)

/-- A morphism between constant derived sheaves is locally induced at `X` when it is induced on
every member of some cover of `X`. -/
@[stacks 09BE "locally induced by coefficient-side derived morphisms"]
def IsLocallyInducedAt {K L : DerivedCategory (ModuleCat.{w} Λ)}
    (φ : (constantSheaf J (ModuleCat.{w} Λ)).mapDerivedCategory.obj K ⟶
      (constantSheaf J (ModuleCat.{w} Λ)).mapDerivedCategory.obj L)
    (X : C) : Prop :=
  ∃ T : J.Cover X, ∀ I : T.Arrow, IsInducedOn φ I.Y

/-- Witness form of `IsInducedOn`. -/
theorem isInducedOn_iff {K L : DerivedCategory (ModuleCat.{w} Λ)}
    (φ : (constantSheaf J (ModuleCat.{w} Λ)).mapDerivedCategory.obj K ⟶
      (constantSheaf J (ModuleCat.{w} Λ)).mapDerivedCategory.obj L)
    (U : C) :
    IsInducedOn φ U ↔
      ∃ α : K ⟶ L,
        CommSq
          (((J.overPullback (ModuleCat.{w} Λ) U).mapDerivedCategory).map φ)
          ((constantSheafOverDerivedIso U).hom.app K)
          ((constantSheafOverDerivedIso U).hom.app L)
          (((constantSheaf (J.over U) (ModuleCat.{w} Λ)).mapDerivedCategory).map α) := sorry

/-- Witness form of `IsLocallyInducedAt`. -/
theorem isLocallyInducedAt_iff {K L : DerivedCategory (ModuleCat.{w} Λ)}
    (φ : (constantSheaf J (ModuleCat.{w} Λ)).mapDerivedCategory.obj K ⟶
      (constantSheaf J (ModuleCat.{w} Λ)).mapDerivedCategory.obj L)
    (X : C) :
    IsLocallyInducedAt φ X ↔
      ∃ T : J.Cover X, ∀ I : T.Arrow, IsInducedOn φ I.Y := sorry

/-- Lemma 21.53.3 (09BE): over a terminal object, a morphism between constant derived sheaves
whose source is perfect is locally induced by morphisms in the coefficient derived category. -/
@[stacks 09BE]
theorem locallyInducedAt_of_isPerfect
    (X : C) (hX : IsTerminal X) (K L : DerivedCategory (ModuleCat.{w} Λ))
    (hK : K.IsPerfect)
    (φ : (constantSheaf J (ModuleCat.{w} Λ)).mapDerivedCategory.obj K ⟶
      (constantSheaf J (ModuleCat.{w} Λ)).mapDerivedCategory.obj L) :
    IsLocallyInducedAt φ X := sorry

end CategoryTheory.Sheaf.DerivedRestriction
