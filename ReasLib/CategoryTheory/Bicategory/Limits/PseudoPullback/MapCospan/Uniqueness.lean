/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.MapCospan.Projections

/-!
# Uniqueness for universal cospan maps

This module exposes the canonical comparison between any presented universal map and
`mapCospan`, together with its forward and inverse comparison formulas.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory.Bicategory.PseudoPullbackCone

open Bicategory
open scoped Pseudofunctor.StrongTrans

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z x' y' z' : B}
variable {f : x ⟶ z} {g : y ⟶ z} {f' : x' ⟶ z'} {g' : y' ⟶ z'}

/-- Any map whose comparison presents the transported source cone is canonically isomorphic to
`mapCospan`. This is the preferred interface for comparing a concrete implementation with the
semantic universal map.
-/
noncomputable abbrev mapCospan.uniqueIso (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') (ψ : CospanTransform f g f' g')
    [T.IsBilimit] (l : S.pt ⟶ T.pt)
    (e : (T.toPseudoCone.comparison S.pt).obj l ≅
      (S.changeCospan ψ).toPseudoCone.π) :
    l ≅ mapCospan S T ψ :=
  lift.uniqueIso (S.changeCospan ψ) T l e

/-- Mapping the forward cell of `mapCospan.uniqueIso` through the represented comparison
recovers the specified presentation followed by the inverse universal comparison.
-/
@[simp]
theorem mapCospan.uniqueIso.map_hom (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') (ψ : CospanTransform f g f' g')
    [T.IsBilimit] (l : S.pt ⟶ T.pt)
    (e : (T.toPseudoCone.comparison S.pt).obj l ≅
      (S.changeCospan ψ).toPseudoCone.π) :
    (T.toPseudoCone.comparison S.pt).map
        (mapCospan.uniqueIso S T ψ l e).hom =
      (e ≪≫ (mapCospan.comparisonIso S T ψ).symm).hom := sorry

/-- Mapping the inverse cell of `mapCospan.uniqueIso` through the represented comparison
recovers the inverse of the specified presentation composite.
-/
@[simp]
theorem mapCospan.uniqueIso.map_inv (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') (ψ : CospanTransform f g f' g')
    [T.IsBilimit] (l : S.pt ⟶ T.pt)
    (e : (T.toPseudoCone.comparison S.pt).obj l ≅
      (S.changeCospan ψ).toPseudoCone.π) :
    (T.toPseudoCone.comparison S.pt).map
        (mapCospan.uniqueIso S T ψ l e).inv =
      (e ≪≫ (mapCospan.comparisonIso S T ψ).symm).inv := sorry

/-- The forward uniqueness comparison transports the first-leg projection from a presented map
to the canonical `mapCospan` projection. -/
@[simp]
theorem mapCospan.uniqueIso.hom_fst (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') (ψ : CospanTransform f g f' g')
    [T.IsBilimit] (l : S.pt ⟶ T.pt)
    (e : (T.toPseudoCone.comparison S.pt).obj l ≅
      (S.changeCospan ψ).toPseudoCone.π) :
    (mapCospan.uniqueIso S T ψ l e).hom ▷ T.fst =
      (Pseudofunctor.StrongTrans.isoApp e
        (LocallyDiscrete.mk Limits.WalkingCospan.left)).hom ≫
        (mapCospan.fstIso S T ψ).inv := sorry

/-- The inverse uniqueness comparison transports the canonical first-leg projection back to a
presented map. -/
@[simp]
theorem mapCospan.uniqueIso.inv_fst (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') (ψ : CospanTransform f g f' g')
    [T.IsBilimit] (l : S.pt ⟶ T.pt)
    (e : (T.toPseudoCone.comparison S.pt).obj l ≅
      (S.changeCospan ψ).toPseudoCone.π) :
    (mapCospan.uniqueIso S T ψ l e).inv ▷ T.fst =
      (mapCospan.fstIso S T ψ).hom ≫
        (Pseudofunctor.StrongTrans.isoApp e
          (LocallyDiscrete.mk Limits.WalkingCospan.left)).inv := sorry

/-- The forward uniqueness comparison transports the second-leg projection from a presented map
to the canonical `mapCospan` projection. -/
@[simp]
theorem mapCospan.uniqueIso.hom_snd (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') (ψ : CospanTransform f g f' g')
    [T.IsBilimit] (l : S.pt ⟶ T.pt)
    (e : (T.toPseudoCone.comparison S.pt).obj l ≅
      (S.changeCospan ψ).toPseudoCone.π) :
    (mapCospan.uniqueIso S T ψ l e).hom ▷ T.snd =
      (Pseudofunctor.StrongTrans.isoApp e
        (LocallyDiscrete.mk Limits.WalkingCospan.right)).hom ≫
        (mapCospan.sndIso S T ψ).inv := sorry

/-- The inverse uniqueness comparison transports the canonical second-leg projection back to a
presented map. -/
@[simp]
theorem mapCospan.uniqueIso.inv_snd (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') (ψ : CospanTransform f g f' g')
    [T.IsBilimit] (l : S.pt ⟶ T.pt)
    (e : (T.toPseudoCone.comparison S.pt).obj l ≅
      (S.changeCospan ψ).toPseudoCone.π) :
    (mapCospan.uniqueIso S T ψ l e).inv ▷ T.snd =
      (mapCospan.sndIso S T ψ).hom ≫
        (Pseudofunctor.StrongTrans.isoApp e
          (LocallyDiscrete.mk Limits.WalkingCospan.right)).inv := sorry

/-- The forward uniqueness comparison transports the central leg from a presented map to the
canonical `mapCospan` central comparison. -/
@[simp]
theorem mapCospan.uniqueIso.hom_base (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') (ψ : CospanTransform f g f' g')
    [T.IsBilimit] (l : S.pt ⟶ T.pt)
    (e : (T.toPseudoCone.comparison S.pt).obj l ≅
      (S.changeCospan ψ).toPseudoCone.π) :
    (mapCospan.uniqueIso S T ψ l e).hom ▷ (T.fst ≫ f') =
      (Pseudofunctor.StrongTrans.isoApp e
        (LocallyDiscrete.mk Limits.WalkingCospan.one)).hom ≫
        (mapCospan.baseIso S T ψ).inv := sorry

/-- The inverse uniqueness comparison transports the canonical central comparison back to a
presented map. -/
@[simp]
theorem mapCospan.uniqueIso.inv_base (S : PseudoPullbackCone f g)
    (T : PseudoPullbackCone f' g') (ψ : CospanTransform f g f' g')
    [T.IsBilimit] (l : S.pt ⟶ T.pt)
    (e : (T.toPseudoCone.comparison S.pt).obj l ≅
      (S.changeCospan ψ).toPseudoCone.π) :
    (mapCospan.uniqueIso S T ψ l e).inv ▷ (T.fst ≫ f') =
      (mapCospan.baseIso S T ψ).hom ≫
        (Pseudofunctor.StrongTrans.isoApp e
          (LocallyDiscrete.mk Limits.WalkingCospan.one)).inv := sorry

end CategoryTheory.Bicategory.PseudoPullbackCone
