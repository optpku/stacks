/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.AtPrime
public import Mathlib.RingTheory.KrullDimension.Module
public import ReasLib.RingTheory.Depth

@[expose] public section

/-!
# Depth and Localization

@stack 0FCC

This file provides the basic comparison between the depth of a finite module over a local ring
and its depth after localization at a prime.
-/

universe u v

open scoped ENat

namespace Module

/-- The depth of a finite module over a Noetherian local ring is at most its depth at a prime
plus the Krull dimension of the corresponding quotient ring. -/
@[stacks 0FCC]
theorem moduleDepth_le_atPrime_add_quotientDim
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (p : Ideal R) [p.IsPrime] :
    (.some (moduleDepth R M) : WithBot ℕ∞) ≤
      .some (moduleDepth (Localization.AtPrime p) (LocalizedModule.AtPrime p M)) +
        ringKrullDim (R ⧸ p) := sorry

end Module
