/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Composition

/-!
# Naturality of full-subcategory composition comparisons

The comparison between restriction of a composite and composition of the
restrictions is natural in both ambient functors.  One-variable forms are
provided for downstream rewriting without horizontal-composition boilerplate.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.ObjectProperty.FullSubcategory.restrict.compIso

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E]
variable {P : ObjectProperty C} {Q : ObjectProperty D}
variable {R : ObjectProperty E}

/-- The restriction composition comparison is natural in both ambient
functors. -/
@[reassoc, stacks 001D "naturality of full-subcategory restriction composition"]
theorem naturality
    {F F' : C ⥤ D} (α : F ⟶ F') {G G' : D ⥤ E} (β : G ⟶ G')
    (hF : P ≤ Q.inverseImage F) (hF' : P ≤ Q.inverseImage F')
    (hG : Q ≤ R.inverseImage G) (hG' : Q ≤ R.inverseImage G') :
    natTrans (mapsToComp hF hG) (mapsToComp hF' hG')
        (NatTrans.hcomp α β) ≫
        (compIso F' G' hF' hG').hom =
      (compIso F G hF hG).hom ≫
        NatTrans.hcomp (natTrans hF hF' α) (natTrans hG hG' β) := sorry

/-- The inverse restriction composition comparison is natural in both
ambient functors. -/
@[reassoc]
theorem inv_naturality
    {F F' : C ⥤ D} (α : F ⟶ F') {G G' : D ⥤ E} (β : G ⟶ G')
    (hF : P ≤ Q.inverseImage F) (hF' : P ≤ Q.inverseImage F')
    (hG : Q ≤ R.inverseImage G) (hG' : Q ≤ R.inverseImage G') :
    NatTrans.hcomp (natTrans hF hF' α) (natTrans hG hG' β) ≫
        (compIso F' G' hF' hG').inv =
      (compIso F G hF hG).inv ≫
        natTrans (mapsToComp hF hG) (mapsToComp hF' hG')
          (NatTrans.hcomp α β) := sorry

/-- The restriction composition comparison is natural in the first ambient
functor. -/
@[reassoc]
theorem naturality_left
    {F F' : C ⥤ D} (α : F ⟶ F') (G : D ⥤ E)
    (hF : P ≤ Q.inverseImage F) (hF' : P ≤ Q.inverseImage F')
    (hG : Q ≤ R.inverseImage G) :
    natTrans (mapsToComp hF hG) (mapsToComp hF' hG)
        (Functor.whiskerRight α G) ≫
        (compIso F' G hF' hG).hom =
      (compIso F G hF hG).hom ≫
        Functor.whiskerRight (natTrans hF hF' α) (restrict G hG) := sorry

/-- The restriction composition comparison is natural in the second ambient
functor. -/
@[reassoc]
theorem naturality_right
    (F : C ⥤ D) {G G' : D ⥤ E} (β : G ⟶ G')
    (hF : P ≤ Q.inverseImage F)
    (hG : Q ≤ R.inverseImage G) (hG' : Q ≤ R.inverseImage G') :
    natTrans (mapsToComp hF hG) (mapsToComp hF hG')
        (Functor.whiskerLeft F β) ≫
        (compIso F G' hF hG').hom =
      (compIso F G hF hG).hom ≫
        Functor.whiskerLeft (restrict F hF) (natTrans hG hG' β) := sorry

/-- The inverse restriction composition comparison is natural in the first
ambient functor. -/
@[reassoc]
theorem inv_naturality_left
    {F F' : C ⥤ D} (α : F ⟶ F') (G : D ⥤ E)
    (hF : P ≤ Q.inverseImage F) (hF' : P ≤ Q.inverseImage F')
    (hG : Q ≤ R.inverseImage G) :
    Functor.whiskerRight (natTrans hF hF' α) (restrict G hG) ≫
        (compIso F' G hF' hG).inv =
      (compIso F G hF hG).inv ≫
        natTrans (mapsToComp hF hG) (mapsToComp hF' hG)
          (Functor.whiskerRight α G) := sorry

/-- The inverse restriction composition comparison is natural in the second
ambient functor. -/
@[reassoc]
theorem inv_naturality_right
    (F : C ⥤ D) {G G' : D ⥤ E} (β : G ⟶ G')
    (hF : P ≤ Q.inverseImage F)
    (hG : Q ≤ R.inverseImage G) (hG' : Q ≤ R.inverseImage G') :
    Functor.whiskerLeft (restrict F hF) (natTrans hG hG' β) ≫
        (compIso F G' hF hG').inv =
      (compIso F G hF hG).inv ≫
        natTrans (mapsToComp hF hG) (mapsToComp hF hG')
          (Functor.whiskerLeft F β) := sorry

end CategoryTheory.ObjectProperty.FullSubcategory.restrict.compIso
