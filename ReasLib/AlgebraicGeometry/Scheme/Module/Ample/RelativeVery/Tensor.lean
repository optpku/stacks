/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.RelativeVery
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

/-!
# Tensor products and relative very ampleness

This module records eventual relative very ampleness after tensoring an invertible module with
high tensor powers of a relatively ample module.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RelativelyAmple

/-- For a finite-type morphism over a quasi-compact base, tensoring an invertible module with
sufficiently high powers of a relatively ample module produces a relatively very ample module. -/
theorem eventually_relativelyVeryAmple_tensor_tensorPow
    {X S : Scheme.{u}} {f : X ⟶ S} {N L : X.Modules}
    [CompactSpace S] [Scheme.Hom.FiniteType f] [Scheme.Modules.Invertible N]
    (hL : RelativelyAmple f L) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      RelativelyVeryAmple f (N ⊗ RingedSpace.TensorPower.sheaf L d) := sorry

end AlgebraicGeometry.RelativelyAmple
