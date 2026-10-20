/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Basic
public import ReasLib.Algebra.PolynomialSite.Differentials
public import ReasLib.CategoryTheory.ObjectProperty.Over.Basic

/-!
# Additive presheaves on the polynomial site

Polynomial algebra augmentations carry the additive presheaves of source rings,
constant target rings, and untensored Kähler differentials.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u

namespace CommAlgCat.Over.Polynomial.Site

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- The additive presheaf sending a polynomial augmentation to its source ring. -/
abbrev structureAbelianPresheaf : (Algebra.PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (unopUnop (Algebra.PolynomialOver A B) ⋙
    ObjectProperty.Over.forgetDiagram (Algebra.isPolynomialOver A B) ⋙
      forget₂ (CommAlgCat A) CommRingCat) ⋙
    forget₂ CommRingCat RingCat.{u} ⋙ forget₂ RingCat AddCommGrpCat.{u}

/-- The constant additive presheaf with value the target ring of the polynomial site. -/
abbrev constantAbelianPresheaf : (Algebra.PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  ((Functor.const (Algebra.PolynomialSite A B)ᵒᵖ).obj (CommRingCat.of B)) ⋙
    forget₂ CommRingCat RingCat.{u} ⋙ forget₂ RingCat AddCommGrpCat.{u}

variable {A B}

/-- The additive group of Kähler differentials of a polynomial augmentation over the base. -/
def kaehlerObj (X : Algebra.PolynomialOver A B) : AddCommGrpCat.{u} :=
  AddCommGrpCat.of (Ω[X.obj.left ⁄ A])

/-- The map on Kähler groups induced by a morphism of polynomial augmentations. -/
def kaehlerMap {X Y : Algebra.PolynomialOver A B} (f : X ⟶ Y) :
    kaehlerObj X ⟶ kaehlerObj Y :=
  AddCommGrpCat.ofHom
    (@KaehlerDifferential.map A A _ _ _ X.obj.left Y.obj.left
      _ _ _ (algebraOfHom f) _ _ (algebraOfHom_isScalarTower f) _ _).toAddMonoidHom

/-- The induced Kähler map sends a universal differential to the differential of its image. -/
theorem kaehlerMap_D {X Y : Algebra.PolynomialOver A B} (f : X ⟶ Y) (x : X.obj.left) :
    (kaehlerMap f).hom (KaehlerDifferential.D A X.obj.left x) =
      KaehlerDifferential.D A Y.obj.left (f.hom.left x) := by
  exact @KaehlerDifferential.map_D A A _ _ _ X.obj.left Y.obj.left
    _ _ _ (algebraOfHom f) _ _ (algebraOfHom_isScalarTower f) _ _ x

/-- Identity morphisms act as the identity on Kähler groups. -/
theorem kaehlerMap_id (X : Algebra.PolynomialOver A B) :
    kaehlerMap (𝟙 X) = 𝟙 (kaehlerObj X) :=
  sorry

/-- Composition of polynomial-augmentation morphisms maps to composition of Kähler maps. -/
theorem kaehlerMap_comp {X Y Z : Algebra.PolynomialOver A B} (f : X ⟶ Y) (g : Y ⟶ Z) :
    kaehlerMap (f ≫ g) = kaehlerMap f ≫ kaehlerMap g :=
  sorry

variable (A B) in
/-- The covariant functor of Kähler groups on polynomial augmentations. -/
def kaehlerCov : Algebra.PolynomialOver A B ⥤ AddCommGrpCat.{u} where
  obj := kaehlerObj
  map f := kaehlerMap f
  map_id X := kaehlerMap_id X
  map_comp f g := kaehlerMap_comp f g

/-- The Kähler functor evaluates to the Kähler group of the corresponding augmentation. -/
theorem kaehlerCov_obj (X : Algebra.PolynomialOver A B) :
    (kaehlerCov A B).obj X = kaehlerObj X := rfl

variable (A B) in
/-- The additive presheaf of untensored Kähler differentials on the polynomial site. -/
def kaehlerPresheaf : (Algebra.PolynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  unopUnop (Algebra.PolynomialOver A B) ⋙ kaehlerCov A B

/-- Evaluating the differential presheaf gives the untensored Kähler group over the base. -/
theorem kaehlerPresheaf_obj (X : (Algebra.PolynomialSite A B)ᵒᵖ) :
    (kaehlerPresheaf A B).obj X = kaehlerObj (unop (unop X)) := rfl

/-- Morphisms of the differential presheaf are induced by the underlying augmentation maps. -/
theorem kaehlerPresheaf_map {X Y : (Algebra.PolynomialSite A B)ᵒᵖ} (f : X ⟶ Y) :
    (kaehlerPresheaf A B).map f = kaehlerMap f.unop.unop := rfl

end CommAlgCat.Over.Polynomial.Site
