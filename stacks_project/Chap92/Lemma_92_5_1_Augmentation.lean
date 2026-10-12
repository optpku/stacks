/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Ring.Under.Basic
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# Augmentation of a simplicial object of algebras over B

The canonical map of simplicial sets associated to a simplicial object of `A`-algebra maps
to `B`, assembled from the Over-structure morphisms to the constant simplicial set on the
carrier of `B`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace CommRingCat.Under

/-- The morphism of simplicial sets assembled from the structure maps of a simplicial object
of `A`-algebra maps to `B`, targeting the constant simplicial set on the carrier of `B`. -/
def overAugmentation {A : CommRingCat.{u}} {B : Under A}
    (P : SimplicialObject (Over B)) :
    P ⋙ Over.forget B ⋙ Under.forget A ⋙ forget CommRingCat ⟶
      (SimplicialObject.const (Type u)).obj B :=
  Functor.whiskerLeft P
    (Functor.whiskerRight (Over.forgetCocone B).ι
      (Under.forget A ⋙ forget CommRingCat))

/-- Components of `overAugmentation` are the underlying maps of the given morphisms to `B`. -/
theorem overAugmentation_app {A : CommRingCat.{u}} {B : Under A}
    (P : SimplicialObject (Over B)) (n : SimplexCategoryᵒᵖ) :
    (overAugmentation P).app n =
      (Under.forget A ⋙ forget CommRingCat).map (P.obj n).hom :=
  sorry

end CommRingCat.Under
