/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Setoids.Hom.OneCell

/-!
# `2`-cells of setoid-fibred categories

Underlying based and total natural transformations, together with their reconstruction API.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open Bicategory
open BasedFunctor
open BasedCategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Setoids

variable {X Y : FiberedCategoryOver.Setoids C}

/-- The underlying based natural transformation of a `2`-morphism between morphisms of
setoid-fibred categories. -/
abbrev toBasedNatTrans {F G : X ⟶ Y} (eta : F ⟶ G) :
    toBasedFunctor F ⟶ toBasedFunctor G :=
  eta.hom

/-- Build a `2`-morphism of setoid-fibred morphisms from a based natural transformation. -/
def ofBasedNatTrans {F G : X ⟶ Y}
    (eta : toBasedFunctor F ⟶ toBasedFunctor G) : F ⟶ G :=
  Bicategory.InducedBicategory.mkHom₂ eta

/-- Projecting a `2`-morphism built by `ofBasedNatTrans` recovers the supplied based natural
transformation. -/
@[simp]
theorem ofBasedNatTrans.toBasedNatTrans {F G : X ⟶ Y}
    (eta : toBasedFunctor F ⟶ toBasedFunctor G) :
    toBasedNatTrans (ofBasedNatTrans eta) = eta := sorry

/-- Rebundling the underlying based natural transformation recovers the original `2`-morphism. -/
@[simp]
theorem toBasedNatTrans.ofBasedNatTrans {F G : X ⟶ Y} (eta : F ⟶ G) :
    ofBasedNatTrans (toBasedNatTrans eta) = eta := sorry

/-- Forgetting the identity `2`-morphism gives the identity based natural transformation. -/
@[simp]
theorem toBasedNatTrans.id (F : X ⟶ Y) :
    toBasedNatTrans (𝟙 F) = 𝟙 (toBasedFunctor F) := sorry

/-- Forgetting a composite gives the composite of the underlying based natural
transformations. -/
@[simp]
theorem toBasedNatTrans.comp {F G H : X ⟶ Y} (eta : F ⟶ G) (theta : G ⟶ H) :
    toBasedNatTrans (eta ≫ theta) = toBasedNatTrans eta ≫ toBasedNatTrans theta := sorry

/-- The ordinary natural transformation on total categories underlying a `2`-morphism of
setoid-fibred morphisms. -/
abbrev toNatTrans {F G : X ⟶ Y} (eta : F ⟶ G) :
    toFunctor F ⟶ toFunctor G :=
  (toBasedNatTrans eta).toNatTrans

/-- Every `2`-cell between setoid-fibred morphisms lies over the identity of the source base. -/
theorem TwoCell.app.isHomLiftId
    {F G : X ⟶ Y} (eta : F ⟶ G) (a : X.total) :
    Functor.IsHomLift Y.p (𝟙 (X.p.obj a)) ((toNatTrans eta).app a) := sorry

variable {F G : X ⟶ Y}

/-- The componentwise identity condition, expressed in the canonical transport-aware functor
form. The ambient based natural transformation is the canonical cell projection `τ.hom`. -/
theorem over_id (τ : F ⟶ G) :
    eqToHom (toBasedFunctor F).w.symm ≫
        Functor.whiskerRight τ.hom.toNatTrans Y.p ≫
          eqToHom (toBasedFunctor G).w =
      𝟙 X.p := sorry
/- Proof strategy: apply `BasedNatTrans.over_id` to `τ.hom`; its endpoint transports are exactly
the stored projection equations of `toBasedFunctor F` and `toBasedFunctor G`. -/

end FiberedCategoryOver.Setoids

end CategoryTheory
