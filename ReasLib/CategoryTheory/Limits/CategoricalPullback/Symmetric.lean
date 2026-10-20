/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import Mathlib.CategoryTheory.Products.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Symmetric presentation of a categorical pullback

Comparison between the ordinary iso-comma model `F ⊡ G` and the symmetric diagonal model
`(F.prod G) ⊡ Functor.diag C`.
-/

@[expose] public section

namespace CategoryTheory.Limits

open CategoryTheory.Prod
open CategoricalPullback
open CategoricalPullback.CatCommSqOver
open scoped CategoricalPullback

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

noncomputable section

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]

/- `CategoricalPullback` is the verified owner for both presentations: applied to `F.prod G`
and `Functor.diag C` it gives exactly the quintuple category, while applied to `F` and `G` it
gives the triple category from Example 4.31.3. `CategoricalPullback.functorEquiv` and
`CatCommSqOver.toFunctorToCategoricalPullback` construct the comparison from a square, but
mathlib has no equivalence theorem for this diagonal specialization. The square conversion is
therefore generalized only over its apex and input square; specializing it to the canonical
diagonal pullback square recovers the source functor and gives later items a reusable bridge. -/

/- Operations converting symmetric diagonal squares to ordinary pair squares. -/
namespace CategoricalPullback.CatCommSqOver.Symmetric

/-- Project a square over `F.prod G` and `Functor.diag C` to a square over `F` and `G`.
Objectwise, the two components of the structural isomorphism are combined as `a ≪≫ b.symm`. -/
def toPair (F : A ⥤ C) (G : B ⥤ C)
    {X : Type u₄} [Category.{v₄} X]
    (P : CatCommSqOver (F.prod G) (Functor.diag C) X) :
    CatCommSqOver F G X where
  fst := P.fst ⋙ CategoryTheory.Prod.fst A B
  snd := P.fst ⋙ CategoryTheory.Prod.snd A B
  iso :=
    (Functor.isoWhiskerRight P.iso (CategoryTheory.Prod.fst C C) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft P.snd (Functor.prod'CompFst (𝟭 C) (𝟭 C)) ≪≫
      Functor.rightUnitor _) ≪≫
    (Functor.isoWhiskerRight P.iso (CategoryTheory.Prod.snd C C) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft P.snd (Functor.prod'CompSnd (𝟭 C) (𝟭 C)) ≪≫
      Functor.rightUnitor _).symm

namespace toPair

/-- The first leg of the pair square is the first product projection of the symmetric leg. -/
@[simp]
theorem fst (F : A ⥤ C) (G : B ⥤ C)
    {X : Type u₄} [Category.{v₄} X]
    (P : CatCommSqOver (F.prod G) (Functor.diag C) X) :
    (toPair F G P).fst = P.fst ⋙ CategoryTheory.Prod.fst A B := sorry

/-- The second leg of the pair square is the second product projection of the symmetric leg. -/
@[simp]
theorem snd (F : A ⥤ C) (G : B ⥤ C)
    {X : Type u₄} [Category.{v₄} X]
    (P : CatCommSqOver (F.prod G) (Functor.diag C) X) :
    (toPair F G P).snd = P.fst ⋙ CategoryTheory.Prod.snd A B := sorry

/-- At an object, the pair-square structural isomorphism is the first projection of the
symmetric structural isomorphism followed by the inverse of its second projection. -/
@[simp]
theorem iso.app (F : A ⥤ C) (G : B ⥤ C)
    {X : Type u₄} [Category.{v₄} X]
    (P : CatCommSqOver (F.prod G) (Functor.diag C) X) (x : X) :
    (toPair F G P).iso.app x =
      (CategoryTheory.Prod.fst C C).mapIso (P.iso.app x) ≪≫
        ((CategoryTheory.Prod.snd C C).mapIso (P.iso.app x)).symm := sorry

/-- The forward structural map of the pair square is the first projected structural map
followed by the inverse second projected structural map. -/
@[simp]
theorem iso.hom.app (F : A ⥤ C) (G : B ⥤ C)
    {X : Type u₄} [Category.{v₄} X]
    (P : CatCommSqOver (F.prod G) (Functor.diag C) X) (x : X) :
    (toPair F G P).iso.hom.app x =
      ((CategoryTheory.Prod.fst C C).mapIso (P.iso.app x)).hom ≫
        ((CategoryTheory.Prod.snd C C).mapIso (P.iso.app x)).inv := sorry

/-- The inverse structural map of the pair square is the second projected structural map
followed by the inverse first projected structural map. -/
@[simp]
theorem iso.inv.app (F : A ⥤ C) (G : B ⥤ C)
    {X : Type u₄} [Category.{v₄} X]
    (P : CatCommSqOver (F.prod G) (Functor.diag C) X) (x : X) :
    (toPair F G P).iso.inv.app x =
      ((CategoryTheory.Prod.snd C C).mapIso (P.iso.app x)).hom ≫
        ((CategoryTheory.Prod.fst C C).mapIso (P.iso.app x)).inv := sorry

end toPair

end CategoricalPullback.CatCommSqOver.Symmetric

/- Symmetries between the ordinary and diagonal presentations of categorical pullbacks. -/
namespace CategoricalPullback.Symmetric

/-- The canonical comparison from the symmetric quintuple model
`(F.prod G) ⊡ (Functor.diag C)` to the triple model `F ⊡ G`. On objects it sends
`(A, B, C, a, b)` to `(A, B, a ≪≫ b.symm)`, i.e. to `(A, B, b⁻¹ ∘ a)`. -/
def comparison (F : A ⥤ C) (G : B ⥤ C) :
    (F.prod G) ⊡ (Functor.diag C) ⥤ F ⊡ G :=
  (toFunctorToCategoricalPullback F G _).obj
    (CatCommSqOver.Symmetric.toPair F G
      ((toCatCommSqOver (F.prod G) (Functor.diag C) _).obj (𝟭 _)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The ordinary pullback object is placed over its second image, with the supplied
comparison and an identity as its two structural isomorphisms. -/
def inverse (F : A ⥤ C) (G : B ⥤ C) :
    F ⊡ G ⥤ (F.prod G) ⊡ (Functor.diag C) where
  obj x :=
    { fst := (x.fst, x.snd)
      snd := G.obj x.snd
      iso := x.iso.prod (Iso.refl _) }
  map f :=
    { fst := f.fst ×ₘ f.snd
      snd := G.map f.snd
      w := by sorry }
  map_id := by intros; sorry
  map_comp := by intros; sorry

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The unit keeps both outer objects and uses the inverse second structural map
for the middle object of the symmetric presentation. -/
def unitIso (F : A ⥤ C) (G : B ⥤ C) :
    𝟭 ((F.prod G) ⊡ (Functor.diag C)) ≅ comparison F G ⋙ inverse F G :=
  NatIso.ofComponents
    (fun x ↦ CategoricalPullback.mkIso (CategoryTheory.prod.etaIso x.fst).symm
      (((CategoryTheory.Prod.snd C C).mapIso x.iso).symm) (by sorry))
    (by intros; sorry)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The counit keeps the two objects of the ordinary pullback with identity maps. -/
def counitIso (F : A ⥤ C) (G : B ⥤ C) :
    inverse F G ⋙ comparison F G ≅ 𝟭 (F ⊡ G) :=
  NatIso.ofComponents
    (fun x ↦ CategoricalPullback.mkIso (Iso.refl x.fst) (Iso.refl x.snd) (by sorry))
    (by intros; sorry)

/-- The symmetric and ordinary categorical pullback presentations have actual
mutually inverse functors, retaining the prescribed comparison as the forward functor. -/
def equivalence (F : A ⥤ C) (G : B ⥤ C) :
    (F.prod G) ⊡ (Functor.diag C) ≌ F ⊡ G where
  functor := comparison F G
  inverse := inverse F G
  unitIso := unitIso F G
  counitIso := counitIso F G
  functor_unitIso_comp := by intros; sorry

/-- The equivalence retains the original symmetric comparison. -/
@[simp]
theorem equivalence_functor (F : A ⥤ C) (G : B ⥤ C) :
    (equivalence F G).functor = comparison F G := rfl

/-- The inverse retains the two supplied outer objects. -/
@[simp]
theorem inverse_obj_fst (F : A ⥤ C) (G : B ⥤ C) (x : F ⊡ G) :
    ((inverse F G).obj x).fst = (x.fst, x.snd) := rfl

/-- The inverse chooses the actual second image as the middle object. -/
@[simp]
theorem inverse_obj_snd (F : A ⥤ C) (G : B ⥤ C) (x : F ⊡ G) :
    ((inverse F G).obj x).snd = G.obj x.snd := rfl

/-- The inverse structural isomorphism is the given comparison paired with the identity. -/
@[simp]
theorem inverse_obj_iso (F : A ⥤ C) (G : B ⥤ C) (x : F ⊡ G) :
    ((inverse F G).obj x).iso = x.iso.prod (Iso.refl _) := rfl

/-- The inverse retains both components of a supplied arrow. -/
@[simp]
theorem inverse_map_fst (F : A ⥤ C) (G : B ⥤ C) {x y : F ⊡ G} (f : x ⟶ y) :
    ((inverse F G).map f).fst = f.fst ×ₘ f.snd := rfl

/-- The inverse middle arrow is the image of the supplied second component. -/
@[simp]
theorem inverse_map_snd (F : A ⥤ C) (G : B ⥤ C) {x y : F ⊡ G} (f : x ⟶ y) :
    ((inverse F G).map f).snd = G.map f.snd := rfl

/-- The unit is the identity on both outer objects. -/
@[simp]
theorem unitIso_hom_app_fst (F : A ⥤ C) (G : B ⥤ C)
    (x : (F.prod G) ⊡ (Functor.diag C)) :
    ((unitIso F G).hom.app x).fst = (𝟙 x.fst.fst) ×ₘ (𝟙 x.fst.snd) := rfl

/-- The unit middle arrow is exactly the inverse second structural arrow. -/
@[simp]
theorem unitIso_hom_app_snd (F : A ⥤ C) (G : B ⥤ C)
    (x : (F.prod G) ⊡ (Functor.diag C)) :
    ((unitIso F G).hom.app x).snd = x.iso.inv.snd := rfl

/-- The inverse unit middle arrow is exactly the given second structural arrow. -/
@[simp]
theorem unitIso_inv_app_snd (F : A ⥤ C) (G : B ⥤ C)
    (x : (F.prod G) ⊡ (Functor.diag C)) :
    ((unitIso F G).inv.app x).snd = x.iso.hom.snd := rfl


/-- The counit is the identity on the first outer object. -/
@[simp]
theorem counitIso_hom_app_fst (F : A ⥤ C) (G : B ⥤ C) (x : F ⊡ G) :
    ((counitIso F G).hom.app x).fst = 𝟙 x.fst := rfl

/-- The counit is the identity on the second outer object. -/
@[simp]
theorem counitIso_hom_app_snd (F : A ⥤ C) (G : B ⥤ C) (x : F ⊡ G) :
    ((counitIso F G).hom.app x).snd = 𝟙 x.snd := rfl


namespace comparison

/-- The first object selected by the symmetric comparison is the first entry of the product
object. -/
@[simp]
theorem obj.fst (F : A ⥤ C) (G : B ⥤ C)
    (x : (F.prod G) ⊡ (Functor.diag C)) :
    ((comparison F G).obj x).fst = x.fst.fst := sorry

/-- The second object selected by the symmetric comparison is the second entry of the product
object. -/
@[simp]
theorem obj.snd (F : A ⥤ C) (G : B ⥤ C)
    (x : (F.prod G) ⊡ (Functor.diag C)) :
    ((comparison F G).obj x).snd = x.fst.snd := sorry

/-- The structural isomorphism selected by the symmetric comparison is the first projection of
the symmetric structural isomorphism followed by the inverse of its second projection. -/
@[simp]
theorem obj.iso (F : A ⥤ C) (G : B ⥤ C)
    (x : (F.prod G) ⊡ (Functor.diag C)) :
    ((comparison F G).obj x).iso =
      (CategoryTheory.Prod.fst C C).mapIso x.iso ≪≫
        ((CategoryTheory.Prod.snd C C).mapIso x.iso).symm := sorry

/-- The forward structural map selected by the symmetric comparison is the first projected map
followed by the inverse second projected map. -/
@[simp]
theorem obj.iso.hom (F : A ⥤ C) (G : B ⥤ C)
    (x : (F.prod G) ⊡ (Functor.diag C)) :
    ((comparison F G).obj x).iso.hom =
      ((CategoryTheory.Prod.fst C C).mapIso x.iso).hom ≫
        ((CategoryTheory.Prod.snd C C).mapIso x.iso).inv := sorry

/-- The inverse structural map selected by the symmetric comparison is the second projected map
followed by the inverse first projected map. -/
@[simp]
theorem obj.iso.inv (F : A ⥤ C) (G : B ⥤ C)
    (x : (F.prod G) ⊡ (Functor.diag C)) :
    ((comparison F G).obj x).iso.inv =
      ((CategoryTheory.Prod.snd C C).mapIso x.iso).hom ≫
        ((CategoryTheory.Prod.fst C C).mapIso x.iso).inv := sorry

/-- On morphisms, the symmetric comparison retains the first component of the product map. -/
@[simp]
theorem map.fst (F : A ⥤ C) (G : B ⥤ C)
    {x y : (F.prod G) ⊡ (Functor.diag C)} (f : x ⟶ y) :
    ((comparison F G).map f).fst = f.fst.fst := sorry

/-- On morphisms, the symmetric comparison retains the second component of the product map. -/
@[simp]
theorem map.snd (F : A ⥤ C) (G : B ⥤ C)
    {x y : (F.prod G) ⊡ (Functor.diag C)} (f : x ⟶ y) :
    ((comparison F G).map f).snd = f.fst.snd := sorry

/-- The functor sending a symmetric quintuple
`(A, B, C, a, b)` to `(A, B, b⁻¹ ∘ a)` is an equivalence from
`(F.prod G) ⊡ (Functor.diag C)` to the `2`-fibre-product category `F ⊡ G` of
Example 4.31.3. -/
@[stacks 06RL]
instance isEquivalence
    (F : A ⥤ C) (G : B ⥤ C) :
    (comparison F G).IsEquivalence :=
  (equivalence F G).isEquivalence_functor

end comparison

end CategoricalPullback.Symmetric

end

end CategoryTheory.Limits
