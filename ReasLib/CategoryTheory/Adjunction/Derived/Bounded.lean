module

public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Canonical
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.RightDerived
public import ReasLib.CategoryTheory.Functor.Derived.Adjunction.Restriction
public import ReasLib.CategoryTheory.Functor.Exactness.Additive
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Bounded-below derived adjunctions with an exact left adjoint

An exact left adjoint acts directly on bounded-below derived categories, while its additive right
adjoint is represented by the canonical total right-derived functor.  This file packages the
localization maps and the absolute-derived pair needed to retain the adjunction.  The pair is
supplied canonically once the bounded-below right-derived functor exists, so site, ringed-space,
and module-theoretic developments can specialize one common construction without rebuilding
proof-local pair data.
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
      (HomotopyCategory.Plus.quasiIso C) := sorry

/-- The localization factor for the composite of the derived left and right adjoints. -/
@[stacks 015F "bounded-below left-right composite factor"]
noncomputable abbrev leftRightFactor (L : C ⥤ₑ D) (R : D ⥤ C) [R.Additive]
    [R.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso D)] :
    DerivedCategory.Plus.Qh ⋙ (left L ⋙ right R) ⟶
      L.obj.mapHomotopyCategoryPlus ⋙ (DerivedCategory.Plus.Qh ⋙ right R) :=
  (Functor.associator DerivedCategory.Plus.Qh (left L) (right R)).inv ≫
    Functor.whiskerRight (leftFactor L) (right R)

/-- The localization unit for the composite of the derived right and left adjoints. -/
@[stacks 015A "bounded-below right-left composite unit"]
noncomputable abbrev rightLeftUnit (L : C ⥤ₑ D) (R : D ⥤ C) [R.Additive]
    [R.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso D)] :
    R.mapHomotopyCategoryPlus ⋙ (DerivedCategory.Plus.Qh ⋙ left L) ⟶
      DerivedCategory.Plus.Qh ⋙ (right R ⋙ left L) :=
  Functor.whiskerRight (rightUnit R) (left L) ≫
    (Functor.associator DerivedCategory.Plus.Qh (right R) (left L)).hom

/-- The two absolute-derived conditions needed for an exact-left bounded-below derived
adjunction. -/
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

/-- Exact left actions and canonical bounded-below right-derived actions form the absolute
derived pair required by the derived-adjunction construction. -/
@[stacks 015F "canonical exact-left bounded-below derived pair", instance]
noncomputable instance hasPair (L : C ⥤ₑ D) (R : D ⥤ C) [R.Additive]
    [R.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso D)] :
    HasPair L R := sorry

/-- The bounded-below derived adjunction associated to an exact-left adjoint pair. -/
@[stacks 015F "exact-left bounded-below derived adjunction"]
noncomputable def adjunction (L : C ⥤ₑ D) (R : D ⥤ C) [R.Additive]
    [R.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso D)]
    (adj : L.obj ⊣ R) :
    left L ⊣ right R :=
  @Adjunction.derived
    _ _ _ _ _ _ _ _ _ _
    (Adjunction.mapHomotopyCategoryPlusAdjunction adj)
    DerivedCategory.Plus.Qh DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso C)
    (HomotopyCategory.Plus.quasiIso D)
    inferInstance inferInstance
    (left L) (right R) (leftFactor L) (rightUnit R)
    (left_isLeftDerived L) inferInstance
    (HasPair.leftRight (L := L) (R := R))
    (HasPair.rightLeft (L := L) (R := R))

end CategoryTheory.Adjunction.Derived.Plus
