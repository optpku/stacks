/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Affine.Subring.SquareCubeOrPrimePower

open AlgebraicGeometry CategoryTheory

universe u

/- Proposition 29.46.8: for a ring extension `A ⊆ B`, the affine spectrum map
`Spec(B) ⟶ Spec(A)` is a universal homeomorphism if and only if every finite subset of `B` lies
in a finite sequence of adjunctions whose new generators satisfy, over the preceding subring,
either the square-cube condition or a prime-dependent multiplication-and-power condition. -/
@[stacks 0CNE] #check
  (AlgebraicGeometry.UniversalHomeomorphism.SquareCubeOrPrimePower.specMap_subtype_iff :
    ∀ {B : Type u} [CommRing B] (A : Subring B),
      UniversalHomeomorphism (Spec.map (CommRingCat.ofHom A.subtype)) ↔
        A.IsFilteredBySquareCubeOrPrimePowerAdjunctions)
