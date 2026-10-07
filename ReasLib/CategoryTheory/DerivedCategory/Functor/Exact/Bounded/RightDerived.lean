module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Below.Inclusion
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.Restriction
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Exact functors as bounded-below right-derived models

An exact functor acts directly on bounded-below derived categories.  This leaf records the
factorization through bounded-below localization and compares that exact action with the
canonical total right-derived functor.  The comparison isomorphism is obtained directly from
uniqueness of right-derived functors, so no separate invertibility proof selects inverse data.
-/

@[expose] public section

open CategoryTheory
open ComplexShape

noncomputable section

universe w vA vB uA uB

namespace CategoryTheory.ExactFunctor.Derived.Plus

variable {A : Type uA} {B : Type uB}
  [Category.{vA} A] [Category.{vB} B]
  [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]

/-- After forgetting boundedness, the bounded-below functor induced directly by an exact
functor has the canonical homotopy-localization factorization. -/
@[stacks 015F "bounded-below exact factorization after inclusion"]
noncomputable def factorCompιIso (F : A ⥤ₑ B) :
    F.obj.toBoundedBelowDerived ⋙ DerivedCategory.Plus.ι ≅
      (DerivedCategory.Plus.Qh ⋙ functor F) ⋙ DerivedCategory.Plus.ι :=
  Functor.toBoundedBelowDerived.compInclusionIso F.obj ≪≫
    (Functor.isoWhiskerLeft (HomotopyCategory.Plus.ι A)
      F.obj.mapDerivedCategoryFactorsh).symm ≪≫
    (Functor.associator (HomotopyCategory.Plus.ι A)
      DerivedCategory.Qh F.mapDerivedCategory).symm ≪≫
    (Functor.isoWhiskerRight
      (DerivedCategory.Plus.QhCompιIsoιCompQh A) F.mapDerivedCategory).symm ≪≫
    Functor.associator DerivedCategory.Plus.Qh
      (DerivedCategory.Plus.ι) F.mapDerivedCategory ≪≫
    (Functor.isoWhiskerLeft DerivedCategory.Plus.Qh (compιIso F)).symm ≪≫
    (Functor.associator DerivedCategory.Plus.Qh
      (functor F) DerivedCategory.Plus.ι).symm

/-- The bounded-below functor induced by an exact functor factors canonically through the
bounded-below derived category. -/
@[stacks 015F "bounded-below exact localization factorization"]
noncomputable def factorIso (F : A ⥤ₑ B) :
    F.obj.toBoundedBelowDerived ≅ DerivedCategory.Plus.Qh ⋙ functor F :=
  Functor.fullyFaithfulCancelRight DerivedCategory.Plus.ι (factorCompιIso F)

/-- The direct bounded-below action of an exact functor is a right-derived functor of its
homotopy-level action.  This canonical instance is obtained from the explicit localization
factorization, without choosing an inverse from a separate `IsIso` proof. -/
@[stacks 015F "exact action is a bounded-below right-derived functor"]
noncomputable instance actionIsRightDerived (F : A ⥤ₑ B) :
    (functor F).IsRightDerivedFunctor (factorIso F).hom
      (HomotopyCategory.Plus.quasiIso A) := sorry

/-- The canonical bounded-below total right-derived functor of an exact functor is naturally
isomorphic to its direct exact-derived action. -/
@[stacks 015F "bounded-below exact right-derived comparison isomorphism"]
noncomputable def rightDerivedIso (F : A ⥤ₑ B)
    [F.obj.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)] :
    Functor.RightDerived.Bounded.functor F.obj ≅ functor F :=
  Functor.rightDerivedUnique (Functor.RightDerived.Bounded.functor F.obj) (functor F)
    (Functor.RightDerived.Bounded.unit F.obj) (factorIso F).hom
      (HomotopyCategory.Plus.quasiIso A)

/-- The forward map from the canonical bounded-below right-derived functor of an exact functor
to its direct exact-derived action. -/
@[stacks 015F "bounded-below exact right-derived comparison"]
noncomputable abbrev rightDerivedComparison (F : A ⥤ₑ B)
    [F.obj.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)] :
    Functor.RightDerived.Bounded.functor F.obj ⟶ functor F :=
  (rightDerivedIso F).hom

/-- The exact-model comparison is characterized by the two localization factorizations. -/
@[reassoc, stacks 015F "bounded-below exact right-derived comparison factorization"]
theorem rightDerivedComparison_fac (F : A ⥤ₑ B)
    [F.obj.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)] :
    Functor.RightDerived.Bounded.unit F.obj ≫
        Functor.whiskerLeft DerivedCategory.Plus.Qh (rightDerivedComparison F) =
      (factorIso F).hom := sorry

end CategoryTheory.ExactFunctor.Derived.Plus
