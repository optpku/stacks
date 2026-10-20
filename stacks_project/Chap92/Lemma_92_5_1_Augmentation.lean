/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommRingCat.Under.SimplicialObject.Augmentation

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

#check (CommRingCat.Under.overAugmentation :
  ∀ {A : CommRingCat.{u}} {B : Under A} (P : SimplicialObject (Over B)),
    P ⋙ Over.forget B ⋙ Under.forget A ⋙ forget CommRingCat ⟶
      (SimplicialObject.const (Type u)).obj B)

#check (CommRingCat.Under.overAugmentation_app :
  ∀ {A : CommRingCat.{u}} {B : Under A} (P : SimplicialObject (Over B))
    (n : SimplexCategoryᵒᵖ),
    (overAugmentation P).app n =
      (Under.forget A ⋙ forget CommRingCat).map (P.obj n).hom)

end CommRingCat.Under
