/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Canonical
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.RightDerived
public import ReasLib.CategoryTheory.Functor.Derived.Adjunction.Restriction
public import ReasLib.CategoryTheory.Functor.Exactness.Additive
public import ReasLib.CategoryTheory.Abelian.Injective.Enough
public import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Bounded-below derived adjunctions with an exact left adjoint

An exact left adjoint acts directly on bounded-below derived categories, while its additive right
adjoint is represented by the canonical total right-derived functor.  This file packages the
localization maps and the absolute-derived pair needed to retain the adjunction.  The pair is
supplied canonically when the source of the right adjoint has enough injectives. On injective
complexes the right-derived unit is invertible, and this remains so after the exact left action.
Thus site, ringed-space, and module-theoretic developments can specialize one common construction.
-/

open CategoryTheory

noncomputable section

universe w vC vD uC uD

namespace CategoryTheory.Adjunction.Derived.Plus

variable {C : Type uC} {D : Type uD}
variable [Category.{vC} C] [Category.{vD} D]
variable [Abelian C] [Abelian D]
variable [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]

/-- The bounded-below derived action of an exact left adjoint. -/
@[stacks 015F "exact left adjoint on bounded-below derived categories"]
noncomputable abbrev left (L : C ⥤ₑ D) :
    DerivedCategory.Plus C ⥤ DerivedCategory.Plus D :=
  ExactFunctor.Derived.Plus.functor L

/-- The canonical bounded-below right-derived action of an additive right adjoint. -/
@[stacks 015A "right adjoint on bounded-below derived categories"]
noncomputable abbrev right (R : D ⥤ C) [R.Additive]
    [R.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso D)] :
    DerivedCategory.Plus D ⥤ DerivedCategory.Plus C :=
  Functor.RightDerived.Bounded.functor R

/-- The localization factor of the exact bounded-below left-derived action. -/
@[stacks 015F "exact bounded-below left-derived factor"]
noncomputable abbrev leftFactor (L : C ⥤ₑ D) :
    DerivedCategory.Plus.Qh ⋙ left L ⟶ L.obj.toBoundedBelowDerived :=
  (ExactFunctor.Derived.Plus.factorIso L).inv

/-- The localization unit of the canonical bounded-below right-derived action. -/
@[stacks 015A "bounded-below right-derived unit"]
noncomputable abbrev rightUnit (R : D ⥤ C) [R.Additive]
    [R.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso D)] :
    R.toBoundedBelowDerived ⟶ DerivedCategory.Plus.Qh ⋙ right R :=
  Functor.RightDerived.Bounded.unit R

/-- The exact action is a left-derived model on bounded-below homotopy categories. -/
@[stacks 015F "exact bounded-below action is left derived", instance]
noncomputable instance left_isLeftDerived (L : C ⥤ₑ D) :
    (left L).IsLeftDerivedFunctor (leftFactor L)
      (HomotopyCategory.Plus.quasiIso C) :=
  Functor.isLeftDerivedFunctor_of_inverts (HomotopyCategory.Plus.quasiIso C)
    (left L) (ExactFunctor.Derived.Plus.factorIso L).symm

/-- The localization factor for the composite of the derived left and right adjoints. -/
@[stacks 015F "bounded-below left-right composite factor"]
noncomputable abbrev leftRightFactor (L : C ⥤ₑ D) (R : D ⥤ C) [R.Additive]
    [R.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso D)] :
    DerivedCategory.Plus.Qh ⋙ (left L ⋙ right R) ⟶
      L.obj.mapHomotopyCategoryPlus ⋙ (DerivedCategory.Plus.Qh ⋙ right R) :=
  Adjunction.Derived.leftRightFactor (right R) (leftFactor L)

/-- The localization unit for the composite of the derived right and left adjoints. -/
@[stacks 015A "bounded-below right-left composite unit"]
noncomputable abbrev rightLeftUnit (L : C ⥤ₑ D) (R : D ⥤ C) [R.Additive]
    [R.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso D)] :
    R.mapHomotopyCategoryPlus ⋙ (DerivedCategory.Plus.Qh ⋙ left L) ⟶
      DerivedCategory.Plus.Qh ⋙ (right R ⋙ left L) :=
  Adjunction.Derived.rightLeftUnit (left L) (rightUnit R)

/-- Compatibility facade for `Adjunction.Derived.HasPair` on the bounded-below models.
The two fields retain the original record-construction API; `hasPair_iff_derivedHasPair`
identifies this facade with the common condition. -/
@[stacks 015F "exact-left bounded-below derived adjunction pair"]
class HasPair (L : C ⥤ₑ D) (R : D ⥤ C) [R.Additive]
    [R.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso D)] : Prop where
  /-- The left-right composite remains a left-derived functor. -/
  leftRight :
    (left L ⋙ right R).IsLeftDerivedFunctor (leftRightFactor L R)
      (HomotopyCategory.Plus.quasiIso C)
  /-- The right-left composite remains a right-derived functor. -/
  rightLeft :
    (right R ⋙ left L).IsRightDerivedFunctor (rightLeftUnit L R)
      (HomotopyCategory.Plus.quasiIso D)

attribute [instance] HasPair.leftRight HasPair.rightLeft

/-- The compatibility facade supplies the common derived-pair condition. -/
instance HasPair.toDerivedHasPair {L : C ⥤ₑ D} {R : D ⥤ C} [R.Additive]
    [R.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso D)] [self : HasPair L R] :
    Adjunction.Derived.HasPair (left L) (right R) (leftFactor L) (rightUnit R)
      (HomotopyCategory.Plus.quasiIso C) (HomotopyCategory.Plus.quasiIso D) where
  toIsLeftDerivedFunctor := self.leftRight
  toIsRightDerivedFunctor := self.rightLeft

/-- The legacy fields impose exactly the common pair condition, with no extra hypotheses. -/
theorem hasPair_iff_derivedHasPair (L : C ⥤ₑ D) (R : D ⥤ C) [R.Additive]
    [R.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso D)] :
    HasPair L R ↔
      Adjunction.Derived.HasPair (left L) (right R) (leftFactor L) (rightUnit R)
        (HomotopyCategory.Plus.quasiIso C) (HomotopyCategory.Plus.quasiIso D) := by
  constructor
  · intro h
    exact HasPair.toDerivedHasPair (self := h)
  · intro h
    exact { leftRight := h.toIsLeftDerivedFunctor, rightLeft := h.toIsRightDerivedFunctor }

/-- Exact left actions and canonical bounded-below right-derived actions form the absolute
derived pair required by the derived-adjunction construction. -/
@[stacks 015F "canonical exact-left bounded-below derived pair", instance]
noncomputable instance hasPair [EnoughInjectives D] (L : C ⥤ₑ D) (R : D ⥤ C) [R.Additive]
    [R.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso D)] :
    HasPair L R where
  leftRight := by
    exact Functor.isLeftDerivedFunctor_of_inverts
      (HomotopyCategory.Plus.quasiIso C) (left L ⋙ right R)
      ((Functor.associator DerivedCategory.Plus.Qh (left L) (right R)).symm ≪≫
        Functor.isoWhiskerRight (ExactFunctor.Derived.Plus.factorIso L).symm (right R))
  rightLeft := by
    apply (HomotopyCategory.Plus.localizerMorphism_derives
      (R.mapHomotopyCategoryPlus ⋙ (DerivedCategory.Plus.Qh ⋙ left L))).isRightDerivedFunctor_of_isIso
      (rightLeftUnit L R)
    intro K
    change IsIso ((left L).map
      ((rightUnit R).app ((InjectiveObject.ι D).mapHomotopyCategoryPlus.obj K)) ≫ 𝟙 _)
    have : IsIso ((rightUnit R).app
        ((InjectiveObject.ι D).mapHomotopyCategoryPlus.obj K)) :=
      (HomotopyCategory.Plus.localizerMorphism_derives R.toBoundedBelowDerived).isIso_of_isRightDerivedFunctor
        (rightUnit R) K
    infer_instance

/-- The bounded-below derived adjunction associated to an exact-left adjoint pair. -/
@[stacks 015F "exact-left bounded-below derived adjunction"]
noncomputable def adjunction [EnoughInjectives D] (L : C ⥤ₑ D) (R : D ⥤ C) [R.Additive]
    [R.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso D)]
    (adj : L.obj ⊣ R) :
    left L ⊣ right R :=
  Adjunction.Derived.HasPair.derived
    (Adjunction.mapHomotopyCategoryPlusAdjunction adj)
    (HomotopyCategory.Plus.quasiIso C)
    (HomotopyCategory.Plus.quasiIso D)
    (leftFactor L) (rightUnit R)

end CategoryTheory.Adjunction.Derived.Plus
