/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale

/-!
# Characterization of weakly étale morphisms

A scheme morphism is weakly étale exactly when it and its diagonal are flat.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.WeaklyEtale

/-- A scheme morphism is weakly étale if and only if it and its diagonal are flat. -/
theorem iff_flat_and_flat_diagonal {X Y : Scheme.{u}} (f : X ⟶ Y) :
    WeaklyEtale f ↔ Flat f ∧ Flat (CategoryTheory.Limits.pullback.diagonal f) := sorry

end AlgebraicGeometry.WeaklyEtale
