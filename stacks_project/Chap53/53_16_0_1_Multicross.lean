/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.PowerSeries.Multicross

universe u

#check (Multicross.ring :
  (k : Type u) → [Field k] → (n : ℕ) → Subring (Fin n → PowerSeries k))
