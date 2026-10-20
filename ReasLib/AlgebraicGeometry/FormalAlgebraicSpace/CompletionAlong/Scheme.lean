/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong
public import Mathlib.AlgebraicGeometry.Restrict

/-! # Restriction of scheme completions to open subschemes -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- Transport a closed subset `Z ⊂ V` along `ofOver.pointsHomeomorph` to a closed
subset of `Points (ofOver V)`. -/
def pointsCloseds {S : Scheme.{u}} (V : Over S) (Z : Closeds V.left) :
    Closeds (Points (ofOver V)) where
  carrier := Set.image (ofOver.pointsHomeomorph V) (Z : Set V.left)
  isClosed' := (ofOver.pointsHomeomorph V).isClosedMap (Z : Set V.left) Z.isClosed

/-- A point of `ofOver V` lies in `pointsCloseds V Z` if and only if it is the
image of a point of `Z`. -/
theorem mem_pointsCloseds {S : Scheme.{u}} {V : Over S} {Z : Closeds V.left}
    {x : Points (ofOver V)} :
    x ∈ pointsCloseds V Z ↔ ∃ z ∈ Z, ofOver.pointsEquiv V z = x :=
  sorry

/-- The morphism of completions induced by an open immersion `V' ⟶ V`, from the
completion of `V'` along the preimage of `Z` to the completion of `V` along
`Z`. -/
def restrictAlong {S : Scheme.{u}} {V : Over S} (Z : Closeds V.left)
    (V' : V.left.Opens) :=
  completionAlong.map
    (ofOverMap (Over.homMk (Scheme.Opens.ι V') rfl :
      Over.mk (Scheme.Opens.ι V' ≫ V.hom) ⟶ V)) (pointsCloseds V Z)

/-- Restricting the completion along an open neighbourhood of `V` and then
including into `V` recovers the functor-of-points map of the open immersion. -/
theorem restrictAlong_comp_ι {S : Scheme.{u}} {V : Over S} (Z : Closeds V.left)
    (V' : V.left.Opens) :
    restrictAlong Z V' ≫ completionAlong.ι (ofOver V) (pointsCloseds V Z) =
      completionAlong.ι (ofOver (Over.mk (Scheme.Opens.ι V' ≫ V.hom)))
          ((pointsCloseds V Z).preimage
            (Points.continuous_map (ofOverMap (Over.homMk (Scheme.Opens.ι V') rfl :
              Over.mk (Scheme.Opens.ι V' ≫ V.hom) ⟶ V)))) ≫
        ofOverMap (Over.homMk (Scheme.Opens.ι V') rfl :
          Over.mk (Scheme.Opens.ι V' ≫ V.hom) ⟶ V) :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
