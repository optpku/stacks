/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Functoriality
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Compatibility
import Mathlib.Tactic.CrossRefAttribute

/-!
# Localization-away models for derived completeness

This file owns the constant multiplication tower, its selected derived internal-Hom model, and
the fine-grained vanishing bridges used in the principal form of derived completeness.  The
homotopy-limit assertion is stated through the presentation-independent predicate
`HomotopyLimit.IsOf`; consumers needing the legacy data-bearing `IsDerivedLimit` interface should
construct or retain an explicit Milnor presentation.

The selected closed object is defined for any ambient monoidal structure.  Comparisons with the
canonical multiplication tower and derived localization predicate additionally require a braiding
and an explicit `DerivedTensor.Right.Monoidal.Model`.  The latter identifies ambient right
tensoring with canonical fixed-right derived tensoring; the braiding and
`InternalHom.adjunctionOf H T` then identify the selected internal Hom as its right adjoint.

@stack 091P
-/

@[expose] public section

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace CategoryTheory.DerivedCategory

variable {A : Type u} [CommRing A]

/-- Lemma 15.92.1 (Stacks `091P`): the inverse system
`⋯ ⟶ K ⟶ K ⟶ K` whose transition maps are multiplication by `f`. -/
@[stacks 091P "the localization-away multiplication tower"]
abbrev localizationAwayTower (f : A) (K : DerivedCategory (ModuleCat A)) :
    ℕᵒᵖ ⥤ DerivedCategory (ModuleCat A) :=
  Functor.ofOpSequence (X := fun _ ↦ K) (fun _ ↦ f • 𝟙 K)

section Closed

variable [MonoidalCategory (DerivedCategory (ModuleCat A))]

/-- Lemma 15.92.1 (Stacks `091P`): the selected internal-Hom model
`RHom_A(A_f[0], K)` of the localization-away object `T(K, f)`.

The closed owner is an explicit argument, so this declaration does not install a local or global
`MonoidalClosed` instance. -/
@[stacks 091P "the localization-away derived internal-Hom object"]
noncomputable abbrev localizationAwayT
    (H : MonoidalClosed (DerivedCategory (ModuleCat A)))
    (f : A) (K : DerivedCategory (ModuleCat A)) : DerivedCategory (ModuleCat A) :=
  InternalHom.obj H
    ((DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)).obj
      (ModuleCat.of A (Localization.Away f))) K

/-- Lemma 15.92.1 (Stacks `091P`): `T(K, f)` has the presentation-independent homotopy-limit
property for the multiplication-by-`f` tower. -/
@[stacks 091P "the homotopy-limit presentation of T(K, f)"]
theorem localizationAwayT_isHomotopyLimit
    [BraidedCategory (DerivedCategory (ModuleCat A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat A)))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat A))
    (f : A) (K : DerivedCategory (ModuleCat A)) :
    HomotopyLimit.IsOf (localizationAwayTower f K) (localizationAwayT H f K) := sorry

/-- Lemma 15.92.1 (Stacks `091P`): `T(K, f)` vanishes exactly when every derived morphism from
an `A_f`-complex to `K` vanishes after restriction of scalars. -/
@[stacks 091P "vanishing of the localization-away object"]
theorem localizationAwayT_isZero_iff
    [BraidedCategory (DerivedCategory (ModuleCat A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat A)))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat A))
    (f : A) (K : DerivedCategory (ModuleCat A)) :
    IsZero (localizationAwayT H f K) ↔
      _root_.DerivedCategory.localizationAwayDerivedHomVanishingCondition f K := sorry

/-- Lemma 15.92.1 (Stacks `091P`): the localization-away derived-Hom condition rewritten as
vanishing of `T(K, f)`. -/
@[stacks 091P "the derived localization vanishing criterion"]
theorem localizationAwayDerivedHomVanishingCondition_iff
    [BraidedCategory (DerivedCategory (ModuleCat A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat A)))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat A))
    (f : A) (K : DerivedCategory (ModuleCat A)) :
    _root_.DerivedCategory.localizationAwayDerivedHomVanishingCondition f K ↔
      IsZero (localizationAwayT H f K) := sorry

end Closed

end CategoryTheory.DerivedCategory

namespace ModuleCat

variable {A : Type u} [CommRing A]

/-- Lemma 15.92.1 (Stacks `091P`): the localization-away vanishing condition for a module,
obtained by applying the canonical derived-Hom predicate to its degree-zero object. -/
@[stacks 091P "the module localization-away vanishing condition"]
def moduleLocalizationAwayTVanishing (M : ModuleCat A) (f : A) : Prop :=
  _root_.DerivedCategory.localizationAwayDerivedHomVanishingCondition f
    ((DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)).obj M)

section Closed

variable [MonoidalCategory (DerivedCategory (ModuleCat A))]

/-- Lemma 15.92.1 (Stacks `091P`): module localization-away vanishing is the vanishing of the
degree-zero specialization of `T(K, f)`. -/
@[stacks 091P "the module localization-away vanishing criterion"]
theorem moduleLocalizationAwayTVanishing_iff
    [BraidedCategory (DerivedCategory (ModuleCat A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat A)))
    (T : CategoryTheory.DerivedCategory.DerivedTensor.Right.Monoidal.Model (C := ModuleCat A))
    (M : ModuleCat A) (f : A) :
    moduleLocalizationAwayTVanishing M f ↔
      IsZero (CategoryTheory.DerivedCategory.localizationAwayT H f
        ((DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)).obj M)) := sorry

end Closed

end ModuleCat
