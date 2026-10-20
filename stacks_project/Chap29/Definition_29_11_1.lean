/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import StacksCheckRecall

open AlgebraicGeometry

universe u

/- Definition 29.11.1: a morphism of schemes `f : X ⟶ S` is affine if the inverse image of every
affine open of `S` is an affine open of `X`. -/
@[stacks 01S6] #check (AlgebraicGeometry.isAffineHom_iff :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S),
    IsAffineHom f ↔ ∀ U : S.Opens, IsAffineOpen U → IsAffineOpen (f ⁻¹ᵁ U))
