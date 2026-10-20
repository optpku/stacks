/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Colimit.Point
import Mathlib.Tactic.CrossRefAttribute

/-!
# Sections to derived colimits

This leaf owns the canonical comparison from evaluation of an `A`-valued presheaf at an object
`U` to its derived colimit over `C`. The coefficient-general construction is the reusable owner;
abelian-group and module-valued names are thin source-facing specializations.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite
open scoped CategoryTheory

noncomputable section

universe q q' u v w

namespace CategoryTheory.DerivedColimit

variable {C : Type u} [Category.{v} C]

/-- Naturality of the colimit cocone map from evaluation at `U`. -/
@[stacks 08Q6 "evaluation-to-colimit cocone naturality"]
theorem evaluationToColimit_naturality
    (A : Type w) [Category A] [HasColimitsOfShape Cᵒᵖ A] (U : C)
    {𝒢 ℋ : Cᵒᵖ ⥤ A} (τ : 𝒢 ⟶ ℋ) :
    ((evaluation Cᵒᵖ A).obj (op U)).map τ ≫ colimit.ι ℋ (op U) =
      colimit.ι 𝒢 (op U) ≫ (colim : (Cᵒᵖ ⥤ A) ⥤ A).map τ := sorry

/-- The natural transformation from evaluation at `U` to the presheaf colimit. -/
@[stacks 08Q6 "evaluation-to-colimit natural transformation"]
def evaluationToColimit
    (A : Type w) [Category A] [HasColimitsOfShape Cᵒᵖ A] (U : C) :
    (evaluation Cᵒᵖ A).obj (op U) ⟶ (colim : (Cᵒᵖ ⥤ A) ⥤ A) where
  app 𝒢 := colimit.ι 𝒢 (op U)
  naturality := fun {_ _} τ => evaluationToColimit_naturality A U τ

/-- The homotopy-to-derived comparison induced by the evaluation-to-colimit transformation. -/
@[stacks 08Q6 "evaluation-to-derived-colimit homotopy comparison"]
def evaluationToColimitHomotopyComparison
    (A : Type w) [Category A] [Abelian A]
    [HasDerivedCategory A] [HasDerivedCategory (Cᵒᵖ ⥤ A)]
    [HasColimitsOfShape Cᵒᵖ A] (U : C) :
    Functor.Homotopy.toDerived ((evaluation Cᵒᵖ A).obj (op U)) ⟶
      (categoryOverPointColimitToDerived C A :
        HomotopyCategory (Cᵒᵖ ⥤ A) (up ℤ) ⥤ DerivedCategory A) :=
  Functor.whiskerRight
    (NatTrans.mapHomotopyCategory (evaluationToColimit A U) (up ℤ))
    DerivedCategory.Qh

/-- Evaluation at an object preserves quasi-isomorphisms, so its derived-category lift is a
left-derived functor. -/
@[stacks 08Q6 "evaluation derived-functor law"]
instance evaluationMapDerivedCategory_isLeftDerivedFunctor
    (A : Type w) [Category A] [Abelian A]
    [HasDerivedCategory A] [HasDerivedCategory (Cᵒᵖ ⥤ A)]
    (U : C) :
    (((evaluation Cᵒᵖ A).obj (op U)).mapDerivedCategory).IsLeftDerivedFunctor
      (((evaluation Cᵒᵖ A).obj (op U)).mapDerivedCategoryFactorsh.hom)
      (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ A) (up ℤ)) := sorry

/-- The natural transformation from derived evaluation at `U` to the derived colimit. -/
@[stacks 08Q6 "evaluation-to-derived-colimit comparison"]
noncomputable def evaluationToDerivedColimit
    (A : Type w) [Category A] [Abelian A]
    [HasDerivedCategory A] [HasDerivedCategory (Cᵒᵖ ⥤ A)]
    [HasColimitsOfShape Cᵒᵖ A]
    [Functor.HasLeftDerivedFunctor
      (categoryOverPointColimitToDerived C A :
        HomotopyCategory (Cᵒᵖ ⥤ A) (up ℤ) ⥤ DerivedCategory A)
      (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ A) (up ℤ))]
    (U : C) :
    ((evaluation Cᵒᵖ A).obj (op U)).mapDerivedCategory ⟶
      (categoryOverPointDerivedColimit C A :
        DerivedCategory (Cᵒᵖ ⥤ A) ⥤ DerivedCategory A) :=
  Functor.leftDerivedNatTrans
    ((evaluation Cᵒᵖ A).obj (op U)).mapDerivedCategory
    ((categoryOverPointColimitToDerived C A).totalLeftDerived
      DerivedCategory.Qh (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ A) (up ℤ)))
    ((evaluation Cᵒᵖ A).obj (op U)).mapDerivedCategoryFactorsh.hom
    ((categoryOverPointColimitToDerived C A).totalLeftDerivedCounit
      DerivedCategory.Qh (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ A) (up ℤ)))
    (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ A) (up ℤ))
    (evaluationToColimitHomotopyComparison A U)

/-- The canonical morphism from sections of a complex over `U` to its derived colimit. -/
@[stacks 08Q6 "section complex to derived colimit"]
noncomputable def sectionComplexToDerivedColimit
    (A : Type w) [Category A] [Abelian A]
    [HasDerivedCategory A] [HasDerivedCategory (Cᵒᵖ ⥤ A)]
    [HasColimitsOfShape Cᵒᵖ A]
    [Functor.HasLeftDerivedFunctor
      (categoryOverPointColimitToDerived C A :
        HomotopyCategory (Cᵒᵖ ⥤ A) (up ℤ) ⥤ DerivedCategory A)
      (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ A) (up ℤ))]
    (U : C) (K : CochainComplex (Cᵒᵖ ⥤ A) ℤ) :
    (((evaluation Cᵒᵖ A).obj (op U)).mapDerivedCategory).obj
        (DerivedCategory.Q.obj K) ⟶
      (categoryOverPointDerivedColimit C A).obj (DerivedCategory.Q.obj K) :=
  (evaluationToDerivedColimit A U).app (DerivedCategory.Q.obj K)

/-- Remark 21.39.4 (08Q6), abelian-group specialization. -/
@[stacks 08Q6 "abelian section complex to derived colimit"]
noncomputable abbrev sectionComplexToLeftDerivedColimit
    (U : C) (K : CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat) ℤ)
    [HasDerivedCategory AddCommGrpCat]
    [HasDerivedCategory (Cᵒᵖ ⥤ AddCommGrpCat)]
    [HasColimitsOfShape Cᵒᵖ AddCommGrpCat]
    [Functor.HasLeftDerivedFunctor
      (categoryOverPointColimitToDerived C AddCommGrpCat :
        HomotopyCategory (Cᵒᵖ ⥤ AddCommGrpCat) (up ℤ) ⥤ DerivedCategory AddCommGrpCat)
      (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ AddCommGrpCat) (up ℤ))] :=
  sectionComplexToDerivedColimit AddCommGrpCat U K

/-- Remark 21.39.4 (08Q6), `B`-module specialization. -/
@[stacks 08Q6 "module section complex to derived colimit"]
noncomputable abbrev moduleSectionComplexToLeftDerivedColimit
    {B : Type w} [Ring B] (U : C)
    (K : CochainComplex (Cᵒᵖ ⥤ ModuleCat B) ℤ)
    [HasDerivedCategory (ModuleCat B)]
    [HasDerivedCategory (Cᵒᵖ ⥤ ModuleCat B)]
    [HasColimitsOfShape Cᵒᵖ (ModuleCat B)]
    [Functor.HasLeftDerivedFunctor
      (categoryOverPointColimitToDerived C (ModuleCat B) :
        HomotopyCategory (Cᵒᵖ ⥤ ModuleCat B) (up ℤ) ⥤
          DerivedCategory (ModuleCat B))
      (HomotopyCategory.quasiIso (Cᵒᵖ ⥤ ModuleCat B) (up ℤ))] :=
  sectionComplexToDerivedColimit (ModuleCat B) U K

end CategoryTheory.DerivedColimit
