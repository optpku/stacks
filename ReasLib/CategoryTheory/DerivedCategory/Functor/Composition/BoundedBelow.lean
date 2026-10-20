/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition.BoundedBelow.Localization
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Canonical
public import ReasLib.CategoryTheory.Functor.Derived.Naturality.Right
public import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives

@[expose] public section

/-!
# Composition of Bounded-Below Right Derived Functors

This module specializes the arbitrary-localization comparison to Mathlib's bounded-below derived
categories.  Its main transformation is literally a natural transformation of functors
`D⁺(A) ⥤ D⁺(C)`:

`R(F ⋙ G) ⟶ RF ⋙ RG`.

The comparison data and factorization require only the three relevant total right derived
functors.  Under enough injectives, Mathlib supplies those instances automatically.
-/

open CategoryTheory CategoryTheory.Limits ComplexShape
open scoped CategoryTheory

noncomputable section

universe wA wB wC v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor.RightDerived.Composition.BoundedBelow

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
variable [Abelian A] [Abelian B] [Abelian C]
variable [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
variable [HasDerivedCategory.{wC} C]
variable (F : A ⥤ B) (G : B ⥤ C) [F.Additive] [G.Additive]

/-- Bridge the canonical bounded-below right-derived-functor input to the unfolded homotopy
functor expression used by the localization implementation.  Keeping this one-way instance in
the shared owner prevents implementation-level `mapHomotopyCategoryPlus` parameters from leaking
into downstream APIs. -/
noncomputable instance canonicalHasRightDerivedFunctor
    (F : A ⥤ B)
    [F.Additive]
    [h : F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)] :
    (F.mapHomotopyCategoryPlus ⋙
      (DerivedCategory.Plus.Qh : HomotopyCategory.Plus B ⥤ DerivedCategory.Plus B)).HasRightDerivedFunctor
        (HomotopyCategory.Plus.quasiIso A) := h

section SourceIso

variable {H : A ⥤ C} [H.Additive]
variable [H.toBoundedBelowDerived.HasRightDerivedFunctor
  (HomotopyCategory.Plus.quasiIso A)]
variable [(F ⋙ G).toBoundedBelowDerived.HasRightDerivedFunctor
  (HomotopyCategory.Plus.quasiIso A)]

/-- An underived isomorphism `H ≅ F ⋙ G` canonically identifies the bounded-below total
right-derived functor of `H` with that of `F ⋙ G`. -/
@[stacks 05T4 "bounded-below right-derived source comparison from an underived isomorphism"]
noncomputable def sourceIsoOfIso (hcomp : H ≅ F ⋙ G) :
    H.toBoundedBelowDerived.totalRightDerived
        (DerivedCategory.Plus.Qh : HomotopyCategory.Plus A ⥤ DerivedCategory.Plus A)
        (HomotopyCategory.Plus.quasiIso A) ≅
      (F ⋙ G).toBoundedBelowDerived.totalRightDerived
        (DerivedCategory.Plus.Qh : HomotopyCategory.Plus A ⥤ DerivedCategory.Plus A)
        (HomotopyCategory.Plus.quasiIso A) :=
  RightDerived.mapNatIso
    (DerivedCategory.Plus.Qh : HomotopyCategory.Plus A ⥤ DerivedCategory.Plus A)
    (HomotopyCategory.Plus.quasiIso A)
    (toBoundedBelowDerived.compIsoOfIso F G hcomp ≪≫
      (toBoundedBelowDerived.compIso F G).symm)

/-- The forward map of `sourceIsoOfIso` is the total right-derived transformation induced by
the corresponding isomorphism of bounded-below homotopy functors. -/
@[simp, stacks 05T4]
theorem sourceIsoOfIso_hom (hcomp : H ≅ F ⋙ G) :
    (sourceIsoOfIso F G hcomp).hom =
      RightDerived.mapNatTrans
        (DerivedCategory.Plus.Qh : HomotopyCategory.Plus A ⥤ DerivedCategory.Plus A)
        (HomotopyCategory.Plus.quasiIso A)
        (toBoundedBelowDerived.compIsoOfIso F G hcomp ≪≫
          (toBoundedBelowDerived.compIso F G).symm).hom := sorry

/-- The inverse map of `sourceIsoOfIso` is the total right-derived transformation induced by
the inverse isomorphism of bounded-below homotopy functors. -/
@[simp, stacks 05T4]
theorem sourceIsoOfIso_inv (hcomp : H ≅ F ⋙ G) :
    (sourceIsoOfIso F G hcomp).inv =
      RightDerived.mapNatTrans
        (DerivedCategory.Plus.Qh : HomotopyCategory.Plus A ⥤ DerivedCategory.Plus A)
        (HomotopyCategory.Plus.quasiIso A)
        (toBoundedBelowDerived.compIsoOfIso F G hcomp ≪≫
          (toBoundedBelowDerived.compIso F G).symm).inv := sorry

end SourceIso

section Comparison
variable [F.toBoundedBelowDerived.HasRightDerivedFunctor
  (HomotopyCategory.Plus.quasiIso A)]
variable [(F ⋙ G).toBoundedBelowDerived.HasRightDerivedFunctor
  (HomotopyCategory.Plus.quasiIso A)]
variable [G.toBoundedBelowDerived.HasRightDerivedFunctor
  (HomotopyCategory.Plus.quasiIso B)]

/-- The canonical comparison `R(F ⋙ G) ⟶ RF ⋙ RG` between functors
`D⁺(A) ⥤ D⁺(C)`. -/
@[stacks 015M "bounded-below right-derived composition comparison"]
noncomputable def comparison :
    Functor.RightDerived.Bounded.functor (F ⋙ G) ⟶
      Functor.RightDerived.Bounded.functor F ⋙
        Functor.RightDerived.Bounded.functor G :=
  RightDerived.Composition.Localization.comparison
    (DerivedCategory.Plus.Qh : HomotopyCategory.Plus A ⥤ DerivedCategory.Plus A)
    (DerivedCategory.Plus.Qh : HomotopyCategory.Plus B ⥤ DerivedCategory.Plus B) F G

/-- The comparison `RH ⟶ RF ⋙ RG` obtained from an underived identification
`H ≅ F ⋙ G`. -/
@[stacks 015M "bounded-below right-derived composition comparison from an underived isomorphism"]
noncomputable def comparisonOfIso
    {H : A ⥤ C} [H.Additive]
    [H.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (hcomp : H ≅ F ⋙ G) :
    H.toBoundedBelowDerived.totalRightDerived
        (DerivedCategory.Plus.Qh : HomotopyCategory.Plus A ⥤ DerivedCategory.Plus A)
        (HomotopyCategory.Plus.quasiIso A) ⟶
      (F.mapHomotopyCategoryPlus ⋙
          (DerivedCategory.Plus.Qh : HomotopyCategory.Plus B ⥤ DerivedCategory.Plus B)).totalRightDerived
            (DerivedCategory.Plus.Qh : HomotopyCategory.Plus A ⥤ DerivedCategory.Plus A)
            (HomotopyCategory.Plus.quasiIso A) ⋙
        G.toBoundedBelowDerived.totalRightDerived
          (DerivedCategory.Plus.Qh : HomotopyCategory.Plus B ⥤ DerivedCategory.Plus B)
          (HomotopyCategory.Plus.quasiIso B) :=
  (sourceIsoOfIso F G hcomp).hom ≫ comparison F G

/-- The comparison induced by `H ≅ F ⋙ G` is characterized before localization by the
underived comparison isomorphism, followed by the standard composition comparison. -/
@[reassoc (attr := simp), stacks 015M]
theorem comparisonOfIso_fac
    {H : A ⥤ C} [H.Additive]
    [H.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (hcomp : H ≅ F ⋙ G) :
    H.toBoundedBelowDerived.totalRightDerivedUnit
          (DerivedCategory.Plus.Qh : HomotopyCategory.Plus A ⥤ DerivedCategory.Plus A)
          (HomotopyCategory.Plus.quasiIso A) ≫
        whiskerLeft (DerivedCategory.Plus.Qh :
          HomotopyCategory.Plus A ⥤ DerivedCategory.Plus A)
          (comparisonOfIso F G hcomp) =
      (toBoundedBelowDerived.compIsoOfIso F G hcomp ≪≫
          (toBoundedBelowDerived.compIso F G).symm).hom ≫
        (F ⋙ G).toBoundedBelowDerived.totalRightDerivedUnit
          (DerivedCategory.Plus.Qh : HomotopyCategory.Plus A ⥤ DerivedCategory.Plus A)
          (HomotopyCategory.Plus.quasiIso A) ≫
        whiskerLeft (DerivedCategory.Plus.Qh :
          HomotopyCategory.Plus A ⥤ DerivedCategory.Plus A)
          (comparison F G) := sorry

/-- Componentwise form of the factorization for the comparison induced by
`H ≅ F ⋙ G`. -/
@[reassoc (attr := simp), stacks 015M]
theorem comparisonOfIso_fac_app
    {H : A ⥤ C} [H.Additive]
    [H.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    (hcomp : H ≅ F ⋙ G) (X : HomotopyCategory.Plus A) :
    (H.toBoundedBelowDerived.totalRightDerivedUnit
        (DerivedCategory.Plus.Qh : HomotopyCategory.Plus A ⥤ DerivedCategory.Plus A)
        (HomotopyCategory.Plus.quasiIso A)).app X ≫
      (comparisonOfIso F G hcomp).app (DerivedCategory.Plus.Qh.obj X) =
    (toBoundedBelowDerived.compIsoOfIso F G hcomp ≪≫
        (toBoundedBelowDerived.compIso F G).symm).hom.app X ≫
      ((F ⋙ G).toBoundedBelowDerived.totalRightDerivedUnit
        (DerivedCategory.Plus.Qh : HomotopyCategory.Plus A ⥤ DerivedCategory.Plus A)
        (HomotopyCategory.Plus.quasiIso A)).app X ≫
      (comparison F G).app (DerivedCategory.Plus.Qh.obj X) := sorry

/-- The standard `D⁺` comparison factors the unit of `R(F ⋙ G)` through the canonical
one-stage/two-stage isomorphism and the units defining `RF` and `RG`. -/
@[reassoc, stacks 015M "factorization of the bounded-below derived composition comparison"]
theorem comparison_fac :
    (F ⋙ G).toBoundedBelowDerived.totalRightDerivedUnit
          (DerivedCategory.Plus.Qh : HomotopyCategory.Plus A ⥤ DerivedCategory.Plus A)
          (HomotopyCategory.Plus.quasiIso A) ≫
        whiskerLeft (DerivedCategory.Plus.Qh :
          HomotopyCategory.Plus A ⥤ DerivedCategory.Plus A)
          (comparison F G) =
      (toBoundedBelowDerived.compIso F G).hom ≫
        whiskerLeft F.mapHomotopyCategoryPlus
          (G.toBoundedBelowDerived.totalRightDerivedUnit
            (DerivedCategory.Plus.Qh : HomotopyCategory.Plus B ⥤ DerivedCategory.Plus B)
            (HomotopyCategory.Plus.quasiIso B)) ≫
        (associator F.mapHomotopyCategoryPlus
          (DerivedCategory.Plus.Qh : HomotopyCategory.Plus B ⥤ DerivedCategory.Plus B)
          (G.toBoundedBelowDerived.totalRightDerived
            (DerivedCategory.Plus.Qh : HomotopyCategory.Plus B ⥤ DerivedCategory.Plus B)
            (HomotopyCategory.Plus.quasiIso B))).hom ≫
        whiskerRight
          ((F.mapHomotopyCategoryPlus ⋙
            (DerivedCategory.Plus.Qh : HomotopyCategory.Plus B ⥤ DerivedCategory.Plus B)).totalRightDerivedUnit
                (DerivedCategory.Plus.Qh :
                  HomotopyCategory.Plus A ⥤ DerivedCategory.Plus A)
                (HomotopyCategory.Plus.quasiIso A))
          (G.toBoundedBelowDerived.totalRightDerived
            (DerivedCategory.Plus.Qh : HomotopyCategory.Plus B ⥤ DerivedCategory.Plus B)
            (HomotopyCategory.Plus.quasiIso B)) ≫
        (associator
          (DerivedCategory.Plus.Qh : HomotopyCategory.Plus A ⥤ DerivedCategory.Plus A)
          ((F.mapHomotopyCategoryPlus ⋙
            (DerivedCategory.Plus.Qh : HomotopyCategory.Plus B ⥤ DerivedCategory.Plus B)).totalRightDerived
                (DerivedCategory.Plus.Qh :
                  HomotopyCategory.Plus A ⥤ DerivedCategory.Plus A)
                (HomotopyCategory.Plus.quasiIso A))
          (G.toBoundedBelowDerived.totalRightDerived
            (DerivedCategory.Plus.Qh : HomotopyCategory.Plus B ⥤ DerivedCategory.Plus B)
            (HomotopyCategory.Plus.quasiIso B))).hom := sorry

attribute [simp] comparison_fac comparison_fac_assoc

/-- Componentwise form of the standard `D⁺` composition factorization. -/
@[reassoc (attr := simp), stacks 015M
  "componentwise factorization of the bounded-below derived composition comparison"]
theorem comparison_fac_app (X : HomotopyCategory.Plus A) :
    ((F ⋙ G).toBoundedBelowDerived.totalRightDerivedUnit
        (DerivedCategory.Plus.Qh : HomotopyCategory.Plus A ⥤ DerivedCategory.Plus A)
        (HomotopyCategory.Plus.quasiIso A)).app X ≫
      (comparison F G).app (DerivedCategory.Plus.Qh.obj X) =
    (toBoundedBelowDerived.compIso F G).hom.app X ≫
      (G.toBoundedBelowDerived.totalRightDerivedUnit
        (DerivedCategory.Plus.Qh : HomotopyCategory.Plus B ⥤ DerivedCategory.Plus B)
        (HomotopyCategory.Plus.quasiIso B)).app (F.mapHomotopyCategoryPlus.obj X) ≫
      (G.toBoundedBelowDerived.totalRightDerived
        (DerivedCategory.Plus.Qh : HomotopyCategory.Plus B ⥤ DerivedCategory.Plus B)
        (HomotopyCategory.Plus.quasiIso B)).map
          (((F.mapHomotopyCategoryPlus ⋙
            (DerivedCategory.Plus.Qh : HomotopyCategory.Plus B ⥤ DerivedCategory.Plus B)).totalRightDerivedUnit
                (DerivedCategory.Plus.Qh :
                  HomotopyCategory.Plus A ⥤ DerivedCategory.Plus A)
                (HomotopyCategory.Plus.quasiIso A)).app X) := sorry

/-- Invertibility of a component of the standard `D⁺` comparison is invariant under a
quasi-isomorphism of bounded-below homotopy objects. -/
@[stacks 015M "quasi-isomorphism invariance of derived comparison components"]
theorem comparison_app_isIso_iff_of_quasiIso
    {X Y : HomotopyCategory.Plus A} (f : X ⟶ Y)
    (hf : HomotopyCategory.Plus.quasiIso A f) :
    IsIso ((comparison F G).app (DerivedCategory.Plus.Qh.obj X)) ↔
      IsIso ((comparison F G).app (DerivedCategory.Plus.Qh.obj Y)) := sorry

/-- The standard `D⁺` comparison is an isomorphism exactly when `F` sends every injective object
to a bounded-below right-acyclic object for `G`, once the three derived functors exist. -/
@[stacks 015M "injective acyclicity criterion for derived composition"]
theorem comparison_isIso_iff_injective_rightAcyclic
    [EnoughInjectives A] :
    IsIso (comparison F G) ↔
      ∀ (I : A) [Injective I], RightAcyclic.Bounded G (F.obj I) := sorry

end Comparison

namespace Comparison

/-- Short namespaced entry point for the injective right-acyclicity criterion for the bounded-below
derived composition comparison. -/
@[stacks 015M "namespaced injective acyclicity criterion"]
theorem isIso_iff_injective_rightAcyclic
    [F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    [(F ⋙ G).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)]
    [G.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso B)]
    [EnoughInjectives A] :
    IsIso (comparison F G) ↔
      ∀ (I : A) [Injective I], RightAcyclic.Bounded G (F.obj I) := sorry

/-- Short namespaced entry point for the enough-injectives criterion for the bounded-below derived
composition comparison. -/
@[stacks 015M "namespaced derived composition criterion"]
theorem isIso_iff
    [EnoughInjectives A] [EnoughInjectives B]
    [PreservesFiniteLimits F] [PreservesFiniteLimits G] :
    IsIso (comparison F G) ↔
      ∀ (I : A) [Injective I], RightAcyclic.Bounded G (F.obj I) := sorry

end Comparison

/-- Stacks 015M: for left exact functors between abelian categories with enough injectives, the
canonical map `R(F ⋙ G) ⟶ RF ⋙ RG` on `D⁺` is an isomorphism exactly when `F` sends injective
objects to bounded-below right-acyclic objects for `G`. -/
@[stacks 015M]
theorem comparison_isIso_iff
    [EnoughInjectives A] [EnoughInjectives B]
    [PreservesFiniteLimits F] [PreservesFiniteLimits G] :
    IsIso (comparison F G) ↔
      ∀ (I : A) [Injective I], RightAcyclic.Bounded G (F.obj I) := sorry

end CategoryTheory.Functor.RightDerived.Composition.BoundedBelow
