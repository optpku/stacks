/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Artinian ring characterizations

`IsArtinianRing` is the canonical owner of the Artinian-ring predicate.  This
leaf exposes the ideal-valued descending-chain view as a small rewrite-ready
bridge; it does not introduce a second ring predicate or a source-specific
chain structure.
-/

universe u

namespace IsArtinianRing

variable {R : Type u} [Semiring R]

/-- A semiring is Artinian exactly when every descending chain of ideals
stabilizes.  The order-dual monotone map is the canonical encoding of such a
chain, so callers can use this statement without rebuilding an instance. -/
@[stacks 00J5 "ideal descending-chain characterization"]
theorem iff_ideal_antitone_chain_condition :
    IsArtinianRing R ↔
      ∀ (f : ℕ →o (Ideal R)ᵒᵈ),
        ∃ n : ℕ, ∀ m : ℕ, n ≤ m → f n = f m := sorry
/- Proof strategy: specialize `monotone_stabilizes_iff_artinian` to the
self-module `R`, then unfold the canonical abbreviation `IsArtinianRing`. -/

/-- An Artinian semiring supplies stabilization for each ideal-valued
descending chain. -/
@[stacks 00J5 "ideal-chain stabilization"]
theorem antitone_chain_condition [IsArtinianRing R]
    (f : ℕ →o (Ideal R)ᵒᵈ) :
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m → f n = f m := sorry
/- Proof strategy: apply the forward direction of
`iff_ideal_antitone_chain_condition` to `inferInstance` and then evaluate it
at `f`. -/

end IsArtinianRing
