/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.UniversalFirstOrder
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.FormallyUnramified

/-- A formally unramified morphism of schemes admits a universal first-order
thickening of its source over its target. -/
theorem existsUniversalFirstOrderThickening {X Z : Scheme.{u}} (h : Z ⟶ X)
    [FormallyUnramified h] :
    ∃ T : Thickening.Over X,
      T.left = Over.mk h ∧ Thickening.IsUniversalFirstOrder T := sorry

end AlgebraicGeometry.FormallyUnramified
