/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Acyclic.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Below.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition
public import ReasLib.CategoryTheory.NatTrans.IsIso

@[expose] public section

/-!
# Bounded-Below Right-Derived Composition for Arbitrary Localization Models

This module constructs the comparison `R(F ⋙ G) ⟶ RF ⋙ RG` using arbitrary localization
models `QA : K⁺(A) ⥤ DA` and `QB : K⁺(B) ⥤ DB`.  The standard `D⁺` specialization lives in
`ReasLib.CategoryTheory.DerivedCategory.Functor.Composition.BoundedBelow`.
-/

open CategoryTheory ComplexShape
open scoped CategoryTheory

noncomputable section

universe w v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

namespace CategoryTheory.Functor.RightDerived.Composition.Localization

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
variable {DA : Type u₄} {DB : Type u₅}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
variable [Category.{v₄} DA] [Category.{v₅} DB]
variable [Abelian A] [Abelian B] [Abelian C] [HasDerivedCategory.{w} C]
variable (QA : HomotopyCategory.Plus A ⥤ DA)
  [QA.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
variable (QB : HomotopyCategory.Plus B ⥤ DB)
  [QB.IsLocalization (HomotopyCategory.Plus.quasiIso B)]
variable (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]

variable [(F ⋙ G).toBoundedBelowDerived.HasRightDerivedFunctor
  (HomotopyCategory.Plus.quasiIso A)]
variable [(F.mapHomotopyCategoryPlus ⋙ QB).HasRightDerivedFunctor
  (HomotopyCategory.Plus.quasiIso A)]
variable [G.toBoundedBelowDerived.HasRightDerivedFunctor
  (HomotopyCategory.Plus.quasiIso B)]

/-- The bounded-below right-derived composition comparison formed using arbitrary localization
models for the source and intermediate homotopy categories. -/
@[stacks 015M "bounded-below derived composition over arbitrary localization models"]
noncomputable def comparison :
    (F ⋙ G).toBoundedBelowDerived.totalRightDerived QA
        (HomotopyCategory.Plus.quasiIso A) ⟶
      (F.mapHomotopyCategoryPlus ⋙ QB).totalRightDerived QA
          (HomotopyCategory.Plus.quasiIso A) ⋙
        G.toBoundedBelowDerived.totalRightDerived QB
          (HomotopyCategory.Plus.quasiIso B) :=
  rightDerivedDesc
    ((F ⋙ G).toBoundedBelowDerived.totalRightDerived QA
      (HomotopyCategory.Plus.quasiIso A))
    ((F ⋙ G).toBoundedBelowDerived.totalRightDerivedUnit QA
      (HomotopyCategory.Plus.quasiIso A))
    (HomotopyCategory.Plus.quasiIso A)
    ((F.mapHomotopyCategoryPlus ⋙ QB).totalRightDerived QA
        (HomotopyCategory.Plus.quasiIso A) ⋙
      G.toBoundedBelowDerived.totalRightDerived QB
        (HomotopyCategory.Plus.quasiIso B))
    ((toBoundedBelowDerived.compIso F G).hom ≫
      whiskerLeft F.mapHomotopyCategoryPlus
        (G.toBoundedBelowDerived.totalRightDerivedUnit QB
          (HomotopyCategory.Plus.quasiIso B)) ≫
      (associator F.mapHomotopyCategoryPlus QB
        (G.toBoundedBelowDerived.totalRightDerived QB
          (HomotopyCategory.Plus.quasiIso B))).hom ≫
      whiskerRight
        ((F.mapHomotopyCategoryPlus ⋙ QB).totalRightDerivedUnit QA
          (HomotopyCategory.Plus.quasiIso A))
        (G.toBoundedBelowDerived.totalRightDerived QB
          (HomotopyCategory.Plus.quasiIso B)) ≫
      (associator QA
        ((F.mapHomotopyCategoryPlus ⋙ QB).totalRightDerived QA
          (HomotopyCategory.Plus.quasiIso A))
        (G.toBoundedBelowDerived.totalRightDerived QB
          (HomotopyCategory.Plus.quasiIso B))).hom)

/-- The arbitrary-model comparison factors the unit of `R(F ⋙ G)` through the canonical
one-stage/two-stage isomorphism and the units defining `RF` and `RG`. -/
@[reassoc]
theorem comparison_fac :
    (F ⋙ G).toBoundedBelowDerived.totalRightDerivedUnit QA
          (HomotopyCategory.Plus.quasiIso A) ≫
        whiskerLeft QA (comparison QA QB F G) =
      (toBoundedBelowDerived.compIso F G).hom ≫
        whiskerLeft F.mapHomotopyCategoryPlus
          (G.toBoundedBelowDerived.totalRightDerivedUnit QB
            (HomotopyCategory.Plus.quasiIso B)) ≫
        (associator F.mapHomotopyCategoryPlus QB
          (G.toBoundedBelowDerived.totalRightDerived QB
            (HomotopyCategory.Plus.quasiIso B))).hom ≫
        whiskerRight
          ((F.mapHomotopyCategoryPlus ⋙ QB).totalRightDerivedUnit QA
            (HomotopyCategory.Plus.quasiIso A))
          (G.toBoundedBelowDerived.totalRightDerived QB
            (HomotopyCategory.Plus.quasiIso B)) ≫
        (associator QA
          ((F.mapHomotopyCategoryPlus ⋙ QB).totalRightDerived QA
            (HomotopyCategory.Plus.quasiIso A))
          (G.toBoundedBelowDerived.totalRightDerived QB
            (HomotopyCategory.Plus.quasiIso B))).hom := sorry

attribute [simp] comparison_fac comparison_fac_assoc

/-- Componentwise factorization of the arbitrary-localization-model comparison. -/
@[reassoc (attr := simp)]
theorem comparison_fac_app (X : HomotopyCategory.Plus A) :
    ((F ⋙ G).toBoundedBelowDerived.totalRightDerivedUnit QA
        (HomotopyCategory.Plus.quasiIso A)).app X ≫
      (comparison QA QB F G).app (QA.obj X) =
    (toBoundedBelowDerived.compIso F G).hom.app X ≫
      (G.toBoundedBelowDerived.totalRightDerivedUnit QB
        (HomotopyCategory.Plus.quasiIso B)).app (F.mapHomotopyCategoryPlus.obj X) ≫
      (G.toBoundedBelowDerived.totalRightDerived QB
        (HomotopyCategory.Plus.quasiIso B)).map
          (((F.mapHomotopyCategoryPlus ⋙ QB).totalRightDerivedUnit QA
            (HomotopyCategory.Plus.quasiIso A)).app X) := sorry

/-- Invertibility of an arbitrary-model comparison component is invariant under a
quasi-isomorphism of bounded-below homotopy objects. -/
theorem comparison_app_isIso_iff_of_quasiIso
    {X Y : HomotopyCategory.Plus A} (f : X ⟶ Y)
    (hf : HomotopyCategory.Plus.quasiIso A f) :
    IsIso ((comparison QA QB F G).app (QA.obj X)) ↔
      IsIso ((comparison QA QB F G).app (QA.obj Y)) := sorry

/-- For arbitrary localization models, the comparison is an isomorphism exactly when `F` sends
injective objects to bounded-below right-acyclic objects for `G`, provided the source has enough
injectives and the three total right derived functors exist. -/
theorem comparison_isIso_iff_injective_rightAcyclic
    [EnoughInjectives A] :
    IsIso (comparison QA QB F G) ↔
      ∀ (I : A) [Injective I], RightAcyclic.Bounded G (F.obj I) := sorry

end CategoryTheory.Functor.RightDerived.Composition.Localization
