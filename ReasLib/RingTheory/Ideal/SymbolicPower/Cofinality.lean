/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.KrullDimension.Basic
public import ReasLib.RingTheory.Completion.LocalRing
public import ReasLib.RingTheory.Ideal.SymbolicPower

@[expose] public section

universe u

namespace Ideal

/-- In a complete Noetherian local domain, symbolic powers of a prime ideal with
one-dimensional quotient are cofinal with its ordinary powers. -/
theorem exists_symbolicPower_le_pow
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsCompleteLocalRing A] (𝔭 : Ideal A) [𝔭.IsPrime]
    (hdim : ringKrullDim (A ⧸ 𝔭) = 1) (n : ℕ) (hn : 1 ≤ n) :
    ∃ m ≥ n, 𝔭.symbolicPower m ≤ 𝔭 ^ n := sorry

end Ideal
