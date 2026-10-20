module

public import Mathlib.CategoryTheory.Bicategory.Functor.Cat
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Pseudofunctors on opposite locally discrete categories

This module gives base-facing names for the identity and composition constraints of a
pseudofunctor on `LocallyDiscrete Cᵒᵖ`. The wrappers accept arrows in `C`, so applications do not
have to repeat the reversal through `op` and `toLoc`. For pseudofunctors valued in `Cat`, the
objectwise naturality and conjugation formulas are exposed at the same boundary.
-/

@[expose] public section

universe vC uC vD uD

namespace CategoryTheory

open Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type uC} [Category.{vC} C]

/-- Passing a specified composite to the locally discrete opposite reverses its displayed order.

This flexible form is intended for `Pseudofunctor.mapComp'` when the composite arrow has a
source-facing name rather than being written as `g ≫ f`. -/
theorem opToLoc_comp_of_eq
    {A B D : C} (f : B ⟶ D) (g : A ⟶ B) (gf : A ⟶ D) (hgf : g ≫ f = gf) :
    f.op.toLoc ≫ g.op.toLoc = gf.op.toLoc := sorry

/-- An endomorphism identified with the identity becomes the identity in the opposite locally
discrete bicategory.  This is the identity analogue of `opToLoc_comp_of_eq`. -/
theorem opToLoc_id_of_eq
    {U : C} (f : U ⟶ U) (hf : f = 𝟙 U) :
    f.op.toLoc = 𝟙 (LocallyDiscrete.mk (Opposite.op U)) := sorry

namespace Pseudofunctor

variable {D : Type*} [Bicategory D]

/-- The identity comparison of a pseudofunctor on an opposite locally discrete category,
indexed by an object of the underlying category. -/
def mapIdOp (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ D) (U : C) :
    F.map (𝟙 U).op.toLoc ≅ 𝟙 (F.obj (LocallyDiscrete.mk (Opposite.op U))) :=
  F.mapId (LocallyDiscrete.mk (Opposite.op U))

/-- The identity comparison over a specified endomorphism `f` together with an equality
`f = 𝟙 U`.  This form retains the displayed arrow and avoids a separate transport isomorphism. -/
def mapIdOp' (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ D)
    (U : C) (f : U ⟶ U) (hf : f = 𝟙 U) :
    F.map f.op.toLoc ≅ 𝟙 (F.obj (LocallyDiscrete.mk (Opposite.op U))) :=
  F.mapId' f.op.toLoc (opToLoc_id_of_eq f hf)

/-- The composition comparison of a pseudofunctor on an opposite locally discrete category,
written in the order of arrows in the underlying category. -/
def mapCompOp (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ D)
    {A B E : C} (f : B ⟶ E) (g : A ⟶ B) :
    F.map (g ≫ f).op.toLoc ≅ F.map f.op.toLoc ≫ F.map g.op.toLoc :=
  F.mapComp f.op.toLoc g.op.toLoc

/-- Flexible form of `mapCompOp` for a specified composite `gf` equipped with
`hgf : g ≫ f = gf`. -/
def mapCompOp' (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ D)
    {A B E : C} (f : B ⟶ E) (g : A ⟶ B) (gf : A ⟶ E) (hgf : g ≫ f = gf) :
    F.map gf.op.toLoc ≅ F.map f.op.toLoc ≫ F.map g.op.toLoc :=
  F.mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc (opToLoc_comp_of_eq f g gf hgf)

section Cat

variable (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vD, uD})

/-- Naturality of the forward base-facing identity comparison. -/
@[reassoc]
theorem mapIdOp_hom_naturality (U : C)
    {x y : F.obj (LocallyDiscrete.mk (Opposite.op U))} (φ : x ⟶ y) :
    (F.map (𝟙 U).op.toLoc).toFunctor.map φ ≫
        (F.mapIdOp U).hom.toNatTrans.app y =
      (F.mapIdOp U).hom.toNatTrans.app x ≫ φ := sorry

/-- Naturality of the inverse base-facing identity comparison. -/
@[reassoc]
theorem mapIdOp_inv_naturality (U : C)
    {x y : F.obj (LocallyDiscrete.mk (Opposite.op U))} (φ : x ⟶ y) :
    (F.mapIdOp U).inv.toNatTrans.app x ≫
        (F.map (𝟙 U).op.toLoc).toFunctor.map φ =
      φ ≫ (F.mapIdOp U).inv.toNatTrans.app y := sorry

/-- Conjugating identity reindexing to the identity action using the base-facing unit
comparison. -/
@[reassoc]
theorem mapIdOp_naturality_1 (U : C)
    {x y : F.obj (LocallyDiscrete.mk (Opposite.op U))} (φ : x ⟶ y) :
    (F.mapIdOp U).inv.toNatTrans.app x ≫
        (F.map (𝟙 U).op.toLoc).toFunctor.map φ ≫
        (F.mapIdOp U).hom.toNatTrans.app y =
      φ := sorry

/-- Conjugating the identity action to identity reindexing using the base-facing unit
comparison. -/
@[reassoc]
theorem mapIdOp_naturality_2 (U : C)
    {x y : F.obj (LocallyDiscrete.mk (Opposite.op U))} (φ : x ⟶ y) :
    (F.mapIdOp U).hom.toNatTrans.app x ≫
        φ ≫ (F.mapIdOp U).inv.toNatTrans.app y =
      (F.map (𝟙 U).op.toLoc).toFunctor.map φ := sorry

/-- Conjugating standard pseudofunctorial identity reindexing to the identity action. -/
@[reassoc]
theorem mapId_naturality_1 (U : C)
    {x y : F.obj (LocallyDiscrete.mk (Opposite.op U))} (φ : x ⟶ y) :
    (F.mapId (LocallyDiscrete.mk (Opposite.op U))).inv.toNatTrans.app x ≫
        (F.map (𝟙 (LocallyDiscrete.mk (Opposite.op U)))).toFunctor.map φ ≫
        (F.mapId (LocallyDiscrete.mk (Opposite.op U))).hom.toNatTrans.app y =
      φ := sorry

/-- Conjugating the identity action to standard pseudofunctorial identity reindexing. -/
@[reassoc]
theorem mapId_naturality_2 (U : C)
    {x y : F.obj (LocallyDiscrete.mk (Opposite.op U))} (φ : x ⟶ y) :
    (F.mapId (LocallyDiscrete.mk (Opposite.op U))).hom.toNatTrans.app x ≫
        φ ≫
        (F.mapId (LocallyDiscrete.mk (Opposite.op U))).inv.toNatTrans.app y =
      (F.map (𝟙 (LocallyDiscrete.mk (Opposite.op U)))).toFunctor.map φ := sorry

/-- Naturality of the forward base-facing composition comparison. -/
@[reassoc]
theorem mapCompOp_hom_naturality
    {A B E : C} (f : B ⟶ E) (g : A ⟶ B)
    {x y : F.obj (LocallyDiscrete.mk (Opposite.op E))} (φ : x ⟶ y) :
    (F.map (g ≫ f).op.toLoc).toFunctor.map φ ≫
        (F.mapCompOp f g).hom.toNatTrans.app y =
      (F.mapCompOp f g).hom.toNatTrans.app x ≫
        (F.map g.op.toLoc).toFunctor.map
          ((F.map f.op.toLoc).toFunctor.map φ) := sorry

/-- Naturality of the inverse base-facing composition comparison. -/
@[reassoc]
theorem mapCompOp_inv_naturality
    {A B E : C} (f : B ⟶ E) (g : A ⟶ B)
    {x y : F.obj (LocallyDiscrete.mk (Opposite.op E))} (φ : x ⟶ y) :
    (F.map g.op.toLoc).toFunctor.map
          ((F.map f.op.toLoc).toFunctor.map φ) ≫
        (F.mapCompOp f g).inv.toNatTrans.app y =
      (F.mapCompOp f g).inv.toNatTrans.app x ≫
        (F.map (g ≫ f).op.toLoc).toFunctor.map φ := sorry

/-- Conjugation formula from the composite action to the iterated action for the base-facing
composition comparison. -/
@[reassoc]
theorem mapCompOp_naturality_1
    {A B E : C} (f : B ⟶ E) (g : A ⟶ B)
    {x y : F.obj (LocallyDiscrete.mk (Opposite.op E))} (φ : x ⟶ y) :
    (F.mapCompOp f g).inv.toNatTrans.app x ≫
        (F.map (g ≫ f).op.toLoc).toFunctor.map φ ≫
        (F.mapCompOp f g).hom.toNatTrans.app y =
      (F.map g.op.toLoc).toFunctor.map
        ((F.map f.op.toLoc).toFunctor.map φ) := sorry

/-- Conjugation formula from the iterated action to the composite action for the base-facing
composition comparison. -/
@[reassoc]
theorem mapCompOp_naturality_2
    {A B E : C} (f : B ⟶ E) (g : A ⟶ B)
    {x y : F.obj (LocallyDiscrete.mk (Opposite.op E))} (φ : x ⟶ y) :
    (F.mapCompOp f g).hom.toNatTrans.app x ≫
        (F.map g.op.toLoc).toFunctor.map
          ((F.map f.op.toLoc).toFunctor.map φ) ≫
        (F.mapCompOp f g).inv.toNatTrans.app y =
      (F.map (g ≫ f).op.toLoc).toFunctor.map φ := sorry

/-- Naturality of the forward base-facing comparison over a specified composite. -/
@[reassoc]
theorem mapCompOp'_hom_naturality
    {A B E : C} (f : B ⟶ E) (g : A ⟶ B) (gf : A ⟶ E)
    (hgf : g ≫ f = gf)
    {x y : F.obj (LocallyDiscrete.mk (Opposite.op E))} (φ : x ⟶ y) :
    (F.map gf.op.toLoc).toFunctor.map φ ≫
        (F.mapCompOp' f g gf hgf).hom.toNatTrans.app y =
      (F.mapCompOp' f g gf hgf).hom.toNatTrans.app x ≫
        (F.map g.op.toLoc).toFunctor.map
          ((F.map f.op.toLoc).toFunctor.map φ) := sorry

/-- Naturality of the inverse base-facing comparison over a specified composite. -/
@[reassoc]
theorem mapCompOp'_inv_naturality
    {A B E : C} (f : B ⟶ E) (g : A ⟶ B) (gf : A ⟶ E)
    (hgf : g ≫ f = gf)
    {x y : F.obj (LocallyDiscrete.mk (Opposite.op E))} (φ : x ⟶ y) :
    (F.map g.op.toLoc).toFunctor.map
          ((F.map f.op.toLoc).toFunctor.map φ) ≫
        (F.mapCompOp' f g gf hgf).inv.toNatTrans.app y =
      (F.mapCompOp' f g gf hgf).inv.toNatTrans.app x ≫
        (F.map gf.op.toLoc).toFunctor.map φ := sorry

/-- Conjugation from the specified-composite action to the iterated action. -/
@[reassoc]
theorem mapCompOp'_naturality_1
    {A B E : C} (f : B ⟶ E) (g : A ⟶ B) (gf : A ⟶ E)
    (hgf : g ≫ f = gf)
    {x y : F.obj (LocallyDiscrete.mk (Opposite.op E))} (φ : x ⟶ y) :
    (F.mapCompOp' f g gf hgf).inv.toNatTrans.app x ≫
        (F.map gf.op.toLoc).toFunctor.map φ ≫
        (F.mapCompOp' f g gf hgf).hom.toNatTrans.app y =
      (F.map g.op.toLoc).toFunctor.map
        ((F.map f.op.toLoc).toFunctor.map φ) := sorry

/-- Conjugation from the iterated action to the specified-composite action. -/
@[reassoc]
theorem mapCompOp'_naturality_2
    {A B E : C} (f : B ⟶ E) (g : A ⟶ B) (gf : A ⟶ E)
    (hgf : g ≫ f = gf)
    {x y : F.obj (LocallyDiscrete.mk (Opposite.op E))} (φ : x ⟶ y) :
    (F.mapCompOp' f g gf hgf).hom.toNatTrans.app x ≫
        (F.map g.op.toLoc).toFunctor.map
          ((F.map f.op.toLoc).toFunctor.map φ) ≫
        (F.mapCompOp' f g gf hgf).inv.toNatTrans.app y =
      (F.map gf.op.toLoc).toFunctor.map φ := sorry

end Cat

end Pseudofunctor

end CategoryTheory
