/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Ideal.AssociatedGraded.Basic

@[expose] public section

universe u

open IsLocalRing
open Ideal.AssociatedGraded

namespace IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- In a Noetherian local ring with one-dimensional cotangent space, every
associated-graded piece has residue-field dimension one until the pieces
eventually vanish, unless all pieces have dimension one. -/
@[stacks 02EI]
theorem finrank_associatedGradedPiece_eq_one_or_eventually_zero
    (hemb : Module.finrank (ResidueField R) (CotangentSpace R) = 1) :
    (∀ n : ℕ, Module.finrank (ResidueField R) (piece (maximalIdeal R) R n) = 1) ∨
      ∃ N : ℕ,
        (∀ n : ℕ, n < N →
          Module.finrank (ResidueField R) (piece (maximalIdeal R) R n) = 1) ∧
        (∀ n : ℕ, N ≤ n →
          Module.finrank (ResidueField R) (piece (maximalIdeal R) R n) = 0) :=
  sorry

end IsLocalRing
