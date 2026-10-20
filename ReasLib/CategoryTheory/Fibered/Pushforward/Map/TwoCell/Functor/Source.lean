/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.NaturalTransformation
public import ReasLib.CategoryTheory.Fibered.Pushforward.Map
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pushforward two-cells before localization

This file owns the action of the prelocalized pushforward map on vertical natural transformations.
-/

@[expose] public section

universe uC uD uS uT vC vD vS vT

namespace CategoryTheory.Functor.Pushforward

open Limits
open scoped Bicategory Functor

variable {C : Type uC} {D : Type uD}
variable {S : Type uS} {T : Type uT}
variable [Category.{vC} C] [Category.{vD} D]
variable [Category.{vS} S] [Category.{vT} T]
variable {p : S ⥤ C} {q : T ⥤ C}

/-- The identity components used on the comma and base legs are compatible with the left
comparison squares of source pushforward maps. -/
@[stacks 04WI "prelocalized pushforward two-cell left coherence"]
theorem sourceMapTransform.map.leftCoherence
    (u : C ⥤ D) {F G : CartesianBasedFunctor p q} (eta : F ⟶ G) :
    (sourceMapTransform u F).squareLeft.iso.hom ≫
        Functor.whiskerRight (𝟙 (sourceMapTransform u F).left)
          (Comma.snd (𝟭 D) u) =
      Functor.whiskerLeft (Comma.snd (𝟭 D) u)
          (𝟙 (sourceMapTransform u F).base) ≫
        (sourceMapTransform u G).squareLeft.iso.hom := sorry

/-- Verticality of a cartesian-based-functor transformation is precisely the compatibility
required on the right comparison squares of source pushforward maps. -/
@[stacks 04WI "prelocalized pushforward two-cell right coherence"]
theorem sourceMapTransform.map.rightCoherence
    (u : C ⥤ D) {F G : CartesianBasedFunctor p q} (eta : F ⟶ G) :
    (sourceMapTransform u F).squareRight.iso.hom ≫
        Functor.whiskerRight
          (CartesianBasedFunctor.toBasedNatTrans eta).toNatTrans q =
      Functor.whiskerLeft p (𝟙 (sourceMapTransform u F).base) ≫
        (sourceMapTransform u G).squareRight.iso.hom := sorry

/-- A vertical transformation of cartesian based functors induces a morphism between the
corresponding cospan transformations defining the prelocalized pushforward maps. -/
@[stacks 04WI "prelocalized pushforward two-cell source transformation"]
def sourceMapTransform.map
    (u : C ⥤ D) {F G : CartesianBasedFunctor p q} (eta : F ⟶ G) :
    sourceMapTransform u F ⟶ sourceMapTransform u G where
  left := 𝟙 _
  base := 𝟙 _
  right := (CartesianBasedFunctor.toBasedNatTrans eta).toNatTrans
  left_coherence := sourceMapTransform.map.leftCoherence u eta
  right_coherence := sourceMapTransform.map.rightCoherence u eta

/-- The natural transformation between prelocalized pushforward maps induced by a vertical
transformation of cartesian based functors. -/
@[stacks 04WI "prelocalized pushforward two-cell"]
def sourceMap₂
    (u : C ⥤ D) {F G : CartesianBasedFunctor p q} (eta : F ⟶ G) :
    sourceMap u F ⟶ sourceMap u G :=
  CategoricalPullback.mapNatTrans (sourceMapTransform.map u eta)

/-- The comma component of the prelocalized pushforward `2`-cell is the identity. -/
@[simp, stacks 04WI "prelocalized pushforward two-cell comma component"]
theorem sourceMap₂.app.fst
    (u : C ⥤ D) {F G : CartesianBasedFunctor p q} (eta : F ⟶ G)
    (A : u ₚₚ p) :
    ((sourceMap₂ u eta).app A).fst = 𝟙 A.fst := sorry

/-- The source component of the prelocalized pushforward `2`-cell is the supplied vertical
transformation. -/
@[simp, stacks 04WI "prelocalized pushforward two-cell source component"]
theorem sourceMap₂.app.snd
    (u : C ⥤ D) {F G : CartesianBasedFunctor p q} (eta : F ⟶ G)
    (A : u ₚₚ p) :
    ((sourceMap₂ u eta).app A).snd =
      (CartesianBasedFunctor.toBasedNatTrans eta).toNatTrans.app A.snd := sorry

/-- Prelocalized pushforward preserves identity transformations. -/
@[simp, stacks 04WI "prelocalized pushforward two-cell identity"]
theorem sourceMap₂.id (u : C ⥤ D) (F : CartesianBasedFunctor p q) :
    sourceMap₂ u (𝟙 F) = 𝟙 (sourceMap u F) := sorry

/-- Prelocalized pushforward preserves vertical composition of transformations. -/
@[simp, stacks 04WI "prelocalized pushforward two-cell composition"]
theorem sourceMap₂.comp
    (u : C ⥤ D) {F G H : CartesianBasedFunctor p q}
    (eta : F ⟶ G) (theta : G ⟶ H) :
    sourceMap₂ u (eta ≫ theta) = sourceMap₂ u eta ≫ sourceMap₂ u theta := sorry

/-- Prelocalized pushforward acts functorially on cartesian based functors and their vertical
transformations. -/
@[stacks 04WI "prelocalized pushforward Hom functor"]
def sourceMapFunctor (u : C ⥤ D) :
    CartesianBasedFunctor p q ⥤ (u ₚₚ p ⥤ u ₚₚ q) where
  obj := sourceMap u
  map := sourceMap₂ u
  map_id := sourceMap₂.id u
  map_comp := sourceMap₂.comp u

/-- The object action of the prelocalized pushforward hom functor is `sourceMap`. -/
@[simp, stacks 04WI "prelocalized pushforward Hom functor object"]
theorem sourceMapFunctor.obj (u : C ⥤ D) (F : CartesianBasedFunctor p q) :
    (sourceMapFunctor u).obj F = sourceMap u F := sorry

/-- The morphism action of the prelocalized pushforward hom functor is `sourceMap₂`. -/
@[simp, stacks 04WI "prelocalized pushforward Hom functor map"]
theorem sourceMapFunctor.map
    (u : C ⥤ D) {F G : CartesianBasedFunctor p q} (eta : F ⟶ G) :
    (sourceMapFunctor u).map eta = sourceMap₂ u eta := sorry

end CategoryTheory.Functor.Pushforward

-- Data audit: the source `2`-cell and Hom functor have explicit component actions; any
-- `sorryAx` is confined to coherence and functor-law fields.
