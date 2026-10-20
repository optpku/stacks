/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Tactic.MkIffOfInductiveProp
public import Mathlib.Topology.Basic
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap71.Lemma_71_4_6_RelativeAssassin
public import stacks_project.Chap77.«77_7_1_1_IsomorphismFunctor»

/-!
# Impurities of modules on algebraic spaces

An impurity of a module `F` above a point `y` of `Y` is a scheme `T` over `Y`, a
specialization `t' ⤳ t` over `y`, and a relative associated point of `F_T` whose
closure misses the fibre over `t`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- An impurity of an `𝒪_X`-module `F` above a point `y` of `Y` consists of a scheme
`T` over `Y`, a specialization `t' ⤳ t` in `T` with image `y`, and a point `ξ` of
`X_T = T ×_Y X` lying over `t'` that is relatively associated for `F_T` and whose
closure does not meet the fibre over `t`. -/
@[mk_iff]
structure IsImpurity {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (F : X.Modules) (y : Points Y) (T : SchemeOver Y)
    (t' t : T.left.left) (ξ : Points (Limits.pullback f T.hom)) : Prop where
  /-- The selected points of `T` form a specialization `t' ⤳ t`. -/
  specializes : t' ⤳ t
  /-- The special endpoint maps to `y` under `T ⟶ Y`. -/
  mapsToY : Points.map T.hom (ofOver.pointsEquiv T.left t) = y
  /-- The selected point of `X_T` lies over the generic endpoint `t'`. -/
  liesOver :
    Points.map (Limits.pullback.snd f T.hom) ξ = ofOver.pointsEquiv T.left t'
  /-- The selected point lies in the relative assassin of the pulled-back module. -/
  mem_relativeAssassin :
    ξ ∈ relativeAssassin (Limits.pullback.snd f T.hom)
      ((pullback (Limits.pullback.fst f T.hom)).obj F)
  /-- The image of the closure of `{ξ}` does not contain the special endpoint. -/
  not_mem_image_closure :
    ofOver.pointsEquiv T.left t ∉
      Points.map (Limits.pullback.snd f T.hom) '' closure ({ξ} : Set _)

namespace IsImpurity

/-- Package the five defining conditions of an impurity of `F` above `y`. -/
def of {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (F : X.Modules) (y : Points Y) (T : SchemeOver Y)
    (t' t : T.left.left) (ξ : Points (Limits.pullback f T.hom))
    (h_specializes : t' ⤳ t)
    (h_mapsToY : Points.map T.hom (ofOver.pointsEquiv T.left t) = y)
    (h_liesOver :
      Points.map (Limits.pullback.snd f T.hom) ξ = ofOver.pointsEquiv T.left t')
    (h_mem :
      ξ ∈ relativeAssassin (Limits.pullback.snd f T.hom)
        ((pullback (Limits.pullback.fst f T.hom)).obj F))
    (h_not :
      ofOver.pointsEquiv T.left t ∉
        Points.map (Limits.pullback.snd f T.hom) '' closure ({ξ} : Set _)) :
    IsImpurity f F y T t' t ξ where
  specializes := h_specializes
  mapsToY := h_mapsToY
  liesOver := h_liesOver
  mem_relativeAssassin := h_mem
  not_mem_image_closure := h_not

/-- The five defining conditions of an impurity of `F` above `y`. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (F : X.Modules) (y : Points Y) (T : SchemeOver Y)
    (t' t : T.left.left) (ξ : Points (Limits.pullback f T.hom))
    (h : IsImpurity f F y T t' t ξ) :
    t' ⤳ t ∧
      Points.map T.hom (ofOver.pointsEquiv T.left t) = y ∧
        Points.map (Limits.pullback.snd f T.hom) ξ =
          ofOver.pointsEquiv T.left t' ∧
          ξ ∈ relativeAssassin (Limits.pullback.snd f T.hom)
              ((pullback (Limits.pullback.fst f T.hom)).obj F) ∧
            ofOver.pointsEquiv T.left t ∉
              Points.map (Limits.pullback.snd f T.hom) ''
                closure ({ξ} : Set _) :=
  sorry

/-- Packaging the five defining conditions yields an impurity of `F` above `y`. -/
theorem of_spec {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (F : X.Modules) (y : Points Y) (T : SchemeOver Y)
    (t' t : T.left.left) (ξ : Points (Limits.pullback f T.hom))
    (h_specializes : t' ⤳ t)
    (h_mapsToY : Points.map T.hom (ofOver.pointsEquiv T.left t) = y)
    (h_liesOver :
      Points.map (Limits.pullback.snd f T.hom) ξ = ofOver.pointsEquiv T.left t')
    (h_mem :
      ξ ∈ relativeAssassin (Limits.pullback.snd f T.hom)
        ((pullback (Limits.pullback.fst f T.hom)).obj F))
    (h_not :
      ofOver.pointsEquiv T.left t ∉
        Points.map (Limits.pullback.snd f T.hom) '' closure ({ξ} : Set _)) :
    IsImpurity f F y T t' t ξ :=
  sorry

/-- The comparison `X_T ⟶ X_{T_i}` induced by a cone projection `T ⟶ T_i` over `Y`. -/
def pullbackStageMap {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {I : Type u} [Preorder I] {D : OrderDual I ⥤ SchemeOver Y} (c : Cone D)
    (i : I) :
    Limits.pullback f c.pt.hom ⟶ Limits.pullback f (D.obj i).hom :=
  Limits.pullback.map f c.pt.hom f (D.obj i).hom
    (𝟙 X) ((ofOverFunctor S).map (c.π.app i).left) (𝟙 Y)
    ((Category.comp_id f).trans (Category.id_comp f).symm)
    ((Category.comp_id c.pt.hom).trans (CostructuredArrow.w (c.π.app i)).symm)

/-- The comparison `X_T ⟶ X_{T_i}` intertwines the projections to `T` and `T_i`. -/
theorem pullbackStageMap_snd {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {I : Type u} [Preorder I] {D : OrderDual I ⥤ SchemeOver Y}
    (c : Cone D) (i : I) :
    pullbackStageMap f c i ≫ Limits.pullback.snd f (D.obj i).hom =
      Limits.pullback.snd f c.pt.hom ≫ (ofOverFunctor S).map (c.π.app i).left :=
  sorry

end IsImpurity

end AlgebraicGeometry.AlgebraicSpace.Modules

