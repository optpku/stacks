/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Cospan.Modification.Category
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ChangeCospan.Functoriality

/-!
# Pseudofunctor for readable change of cospan

This module assembles the object, morphism, and `2`-morphism actions of a walking-cospan
transformation into a pseudofunctor of readable pseudopullback-cone bicategories.  The identity
and composition comparison owners remain in the `Functoriality` leaves; projection formulas are
kept in `Pseudofunctor.Computations`.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory
open scoped CategoryTheory.Bicategory.CospanTransform

universe w v u

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Bicategory.PseudoPullbackCone

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z x' y' z' : B}
variable {f : x ⟶ z} {g : y ⟶ z} {f' : x' ⟶ z'} {g' : y' ⟶ z'}

namespace Implementation

/-- Changing cospan preserves identity `2`-morphisms of readable pseudo-pullback cones. -/
private theorem changeCospan.map₂_id
    (ψ : CospanTransform f g f' g')
    {S T : PseudoPullbackCone f g} (u : S ⟶ T) :
    changeCospan.map₂ ψ (𝟙 u) =
      𝟙 (changeCospan.map ψ u) := sorry
/- Proof strategy: apply `PseudoPullbackCone.hom₂_ext` and use
`changeCospan.map₂.apex`. -/

/-- Changing cospan preserves vertical composition of readable cone `2`-morphisms. -/
private theorem changeCospan.map₂_comp
    (ψ : CospanTransform f g f' g')
    {S T : PseudoPullbackCone f g} {u v w : S ⟶ T}
    (η : u ⟶ v) (θ : v ⟶ w) :
    changeCospan.map₂ ψ (η ≫ θ) =
      changeCospan.map₂ ψ η ≫ changeCospan.map₂ ψ θ := sorry
/- Proof strategy: apply `PseudoPullbackCone.hom₂_ext` and use
`changeCospan.map₂.apex`. -/

/-- The explicit prelax core of readable change of cospan. -/
private def changeCospan.prelax
    (ψ : CospanTransform f g f' g') :
    PrelaxFunctor (PseudoPullbackCone f g)
      (PseudoPullbackCone f' g') where
  obj S := S.changeCospan ψ
  map := changeCospan.map ψ
  map₂ := changeCospan.map₂ ψ
  map₂_id := changeCospan.map₂_id ψ
  map₂_comp := changeCospan.map₂_comp ψ

/-- Readable change of cospan preserves left whiskering up to its explicit composition
comparisons. -/
private theorem changeCospan.pseudofunctor.map₂_whiskerLeft
    (ψ : CospanTransform f g f' g') :
    ∀ {R S T : PseudoPullbackCone f g} (u : R ⟶ S)
      {v w : S ⟶ T} (η : v ⟶ w),
      (changeCospan.prelax ψ).map₂ (u ◁ η) =
        (changeCospan.mapComp ψ u v).hom ≫
          (changeCospan.prelax ψ).map u ◁
            (changeCospan.prelax ψ).map₂ η ≫
          (changeCospan.mapComp ψ u w).inv := sorry
/- Proof strategy: apply `PseudoPullbackCone.hom₂_ext`; all comparison apex cells are
identities, so the equation reduces to the source whiskering equation. -/

/-- Readable change of cospan preserves right whiskering up to its explicit composition
comparisons. -/
private theorem changeCospan.pseudofunctor.map₂_whiskerRight
    (ψ : CospanTransform f g f' g') :
    ∀ {R S T : PseudoPullbackCone f g} {u v : R ⟶ S}
      (η : u ⟶ v) (w : S ⟶ T),
      (changeCospan.prelax ψ).map₂ (η ▷ w) =
        (changeCospan.mapComp ψ u w).hom ≫
          (changeCospan.prelax ψ).map₂ η ▷
            (changeCospan.prelax ψ).map w ≫
          (changeCospan.mapComp ψ v w).inv := sorry
/- Proof strategy: apply `PseudoPullbackCone.hom₂_ext`; all comparison apex cells are
identities, so the equation reduces to the source whiskering equation. -/

/-- Readable change of cospan preserves associators. -/
private theorem changeCospan.pseudofunctor.map₂_associator
    (ψ : CospanTransform f g f' g') :
    ∀ {Q R S T : PseudoPullbackCone f g}
      (u : Q ⟶ R) (v : R ⟶ S) (w : S ⟶ T),
      (changeCospan.prelax ψ).map₂ (α_ u v w).hom =
        (changeCospan.mapComp ψ (u ≫ v) w).hom ≫
          (changeCospan.mapComp ψ u v).hom ▷
            (changeCospan.prelax ψ).map w ≫
          (α_ ((changeCospan.prelax ψ).map u)
            ((changeCospan.prelax ψ).map v)
            ((changeCospan.prelax ψ).map w)).hom ≫
          (changeCospan.prelax ψ).map u ◁
            (changeCospan.mapComp ψ v w).inv ≫
          (changeCospan.mapComp ψ u (v ≫ w)).inv := sorry
/- Proof strategy: apply `PseudoPullbackCone.hom₂_ext`; identity comparison apex cells reduce
the equation to preservation of the source associator. -/

/-- Readable change of cospan preserves left unitors. -/
private theorem changeCospan.pseudofunctor.map₂_leftUnitor
    (ψ : CospanTransform f g f' g') :
    ∀ {S T : PseudoPullbackCone f g} (u : S ⟶ T),
      (changeCospan.prelax ψ).map₂ (λ_ u).hom =
        (changeCospan.mapComp ψ (𝟙 S) u).hom ≫
          (changeCospan.mapId ψ S).hom ▷
            (changeCospan.prelax ψ).map u ≫
          (λ_ ((changeCospan.prelax ψ).map u)).hom := sorry
/- Proof strategy: apply `PseudoPullbackCone.hom₂_ext`; identity comparison apex cells reduce
the equation to preservation of the source left unitor. -/

/-- Readable change of cospan preserves right unitors. -/
private theorem changeCospan.pseudofunctor.map₂_rightUnitor
    (ψ : CospanTransform f g f' g') :
    ∀ {S T : PseudoPullbackCone f g} (u : S ⟶ T),
      (changeCospan.prelax ψ).map₂ (ρ_ u).hom =
        (changeCospan.mapComp ψ u (𝟙 T)).hom ≫
          (changeCospan.prelax ψ).map u ◁
            (changeCospan.mapId ψ T).hom ≫
          (ρ_ ((changeCospan.prelax ψ).map u)).hom := sorry
/- Proof strategy: apply `PseudoPullbackCone.hom₂_ext`; identity comparison apex cells reduce
the equation to preservation of the source right unitor. -/

end Implementation

/-- Changing the cospan of readable pseudo-pullback cones is a pseudofunctor.

This is the readable walking-cospan facade of the shape-independent
`PseudoCone.postcompose`. It leaves apex maps and apex `2`-morphisms literally unchanged and
uses explicit presentation comparisons to expose the conventional four-field cone data. -/
def changeCospan.pseudofunctor
    (ψ : CospanTransform f g f' g') :
    Pseudofunctor (PseudoPullbackCone f g)
      (PseudoPullbackCone f' g') where
  toPrelaxFunctor := Implementation.changeCospan.prelax ψ
  mapId := changeCospan.mapId ψ
  mapComp := changeCospan.mapComp ψ
  map₂_whisker_left := Implementation.changeCospan.pseudofunctor.map₂_whiskerLeft ψ
  map₂_whisker_right := Implementation.changeCospan.pseudofunctor.map₂_whiskerRight ψ
  map₂_associator := Implementation.changeCospan.pseudofunctor.map₂_associator ψ
  map₂_left_unitor := Implementation.changeCospan.pseudofunctor.map₂_leftUnitor ψ
  map₂_right_unitor := Implementation.changeCospan.pseudofunctor.map₂_rightUnitor ψ

end Bicategory.PseudoPullbackCone

end CategoryTheory
