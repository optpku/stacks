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
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeOver
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints.Relative.Locus

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

end IsImpurity

end AlgebraicGeometry.AlgebraicSpace.Modules
