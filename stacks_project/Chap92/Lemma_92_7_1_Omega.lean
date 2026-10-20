/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.PolynomialSite.Differentials

/-!
# Naive Kähler sheaves on the polynomial site

The differential functor is supplied by its shared mathematical owner.
The compatibility theorems retain the explicit algebra arguments used by existing consumers.
-/

@[expose] public section

open CategoryTheory

universe u

namespace CommAlgCat.Over.Polynomial.Site

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The morphism-induced algebra structure respects the original base, independently of
an additional supplied algebra structure. -/
theorem isScalarTower_algebraOfHom {X Y : Algebra.PolynomialOver A B} (f : X ⟶ Y)
    [Algebra X.obj.left Y.obj.left] :
    @IsScalarTower A X.obj.left Y.obj.left _ (algebraOfHom f).toSMul _ :=
  algebraOfHom_isScalarTower f

/-- The morphism-induced and augmentation-induced actions form a scalar tower,
independently of additional supplied algebra structures. -/
theorem isScalarTower_toBase {X Y : Algebra.PolynomialOver A B} (f : X ⟶ Y)
    [Algebra X.obj.left Y.obj.left] [Algebra Y.obj.left B] [Algebra X.obj.left B] :
    @IsScalarTower X.obj.left Y.obj.left B (algebraOfHom f).toSMul
      (algebraToBase Y).toSMul (algebraToBase X).toSMul :=
  toBase_isScalarTower f

#check (omegaSheaf : (A B : Type u) → [CommRing A] → [CommRing B] → [Algebra A B] →
  (Algebra.PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)

end CommAlgCat.Over.Polynomial.Site
