/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Cones
public import Mathlib.CategoryTheory.Limits.IsLimit
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Base change of cocones of algebraic spaces

A cocone `(X, X_i ⟶ X)` in `Over B` may be recast as a diagram over the apex
`X`, then pulled back along a test morphism `U ⟶ X` to a cocone in `Over B`
with apex `U`. Pairwise overlaps of a family over `X` are the fibre products
`U_a ×_X U_b`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u v w

namespace AlgebraicGeometry.AlgebraicSpace

variable {J : Type v} [Category.{v} J] {S : Scheme.{u}} {B : AlgebraicSpace S}
variable {D : J ⥤ Over B}

/-- The triangle witnessing that a transition map of `D` is a morphism over the
apex of `c`. -/
private theorem toOverApex_w (c : Cocone D) {i j : J} (hij : i ⟶ j) :
    (D.map hij).left ≫ (c.ι.app j).left = (c.ι.app i).left :=
  sorry

/-- The diagram `i ↦ X_i` of a cocone `(X, X_i ⟶ X)`, viewed in the slice over
the apex `X`. -/
def toOverApex (c : Cocone D) : J ⥤ Over c.pt.left :=
  Functor.toOver (D ⋙ Over.forget B) c.pt.left
    (fun i ↦ (c.ι.app i).left) (by
      intro i j hij
      exact toOverApex_w c hij)

/-- The object of `toOverApex c` at `i` is the cocone leg `X_i ⟶ X`. -/
theorem toOverApex_obj (c : Cocone D) (i : J) :
    (toOverApex c).obj i = Over.mk (c.ι.app i).left :=
  sorry

/-- The objects of `toOverApex c` are the cocone legs, and the transition maps
are the underlying morphisms of `D`. -/
theorem toOverApex_spec (c : Cocone D) (i : J) {j : J} (hij : i ⟶ j) :
    (toOverApex c).obj i = Over.mk (c.ι.app i).left ∧
      ((toOverApex c).map hij).left = (D.map hij).left :=
  sorry

/-- The diagram `i ↦ X_i ×_X U` in `Over B`, obtained by pulling back the
cocone legs along `f : U ⟶ X` and postcomposing into `Over B`. -/
def baseChangeDiagram (c : Cocone D) {U : AlgebraicSpace S} (f : U ⟶ c.pt.left) :
    J ⥤ Over B :=
  toOverApex c ⋙ overPullback f ⋙ Over.map (f ≫ c.pt.hom)

/-- The object of `baseChangeDiagram c f` at `i` is `X_i ×_X U` over `B`. -/
theorem baseChangeDiagram_obj (c : Cocone D) {U : AlgebraicSpace S}
    (f : U ⟶ c.pt.left) (i : J) :
    (baseChangeDiagram c f).obj i =
      Over.mk (overPullbackSnd f (Over.mk (c.ι.app i).left) ≫ f ≫ c.pt.hom) :=
  sorry

/-- The triangle witnessing that the second projection of `X_i ×_X U` is a
morphism over `B` from the pulled-back object to `U`. -/
private theorem baseChangeLeg_w (c : Cocone D) {U : AlgebraicSpace S}
    (f : U ⟶ c.pt.left) (i : J) :
    overPullbackSnd f (Over.mk (c.ι.app i).left) ≫ (Over.mk (f ≫ c.pt.hom)).hom =
      ((baseChangeDiagram c f).obj i).hom :=
  sorry

/-- The cocone leg `X_i ×_X U ⟶ U` in `Over B`. -/
def baseChangeLeg (c : Cocone D) {U : AlgebraicSpace S} (f : U ⟶ c.pt.left)
    (i : J) :
    (baseChangeDiagram c f).obj i ⟶ Over.mk (f ≫ c.pt.hom) :=
  Over.homMk (overPullbackSnd f (Over.mk (c.ι.app i).left)) (by
    exact baseChangeLeg_w c f i)

/-- The cocone `U ⇐ (X_i ×_X U)` in `Over B` obtained by base change of `c`
along `f : U ⟶ X`. -/
def baseChangeCocone (c : Cocone D) {U : AlgebraicSpace S}
    (f : U ⟶ c.pt.left) :
    Cocone (baseChangeDiagram c f) where
  pt := Over.mk (f ≫ c.pt.hom)
  ι :=
    { app := fun i ↦ baseChangeLeg c f i
      naturality := fun _ _ _ ↦ sorry }

/-- The apex of `baseChangeCocone c f` is `U` over `B`. -/
theorem baseChangeCocone_pt (c : Cocone D) {U : AlgebraicSpace S}
    (f : U ⟶ c.pt.left) :
    (baseChangeCocone c f).pt = Over.mk (f ≫ c.pt.hom) :=
  sorry

/-- The `i`-th leg of `baseChangeCocone c f` is `baseChangeLeg c f i`. -/
theorem baseChangeCocone_ι (c : Cocone D) {U : AlgebraicSpace S}
    (f : U ⟶ c.pt.left) (i : J) :
    (baseChangeCocone c f).ι.app i = baseChangeLeg c f i :=
  sorry

/-- The canonical morphism `U_a ×_X U_b ⟶ X` of a family over `X`. -/
def overlapHom {X : AlgebraicSpace S} {ι : Type w} (family : ι → Over X)
    (a b : ι) :
    overPullbackObj (family b).hom (family a) ⟶ X :=
  overPullbackFst (family b).hom (family a) ≫ (family a).hom

/-- The overlap morphism equals both projections composed with the family
maps to `X`. -/
theorem overlapHom_spec {X : AlgebraicSpace S} {ι : Type w}
    (family : ι → Over X) (a b : ι) :
    overlapHom family a b =
        overPullbackFst (family b).hom (family a) ≫ (family a).hom ∧
      overlapHom family a b =
        overPullbackSnd (family b).hom (family a) ≫ (family b).hom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
