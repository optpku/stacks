/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.AdicAlgebraSystem

@[expose] public section

universe u

#check (AdicAlgebraSystem.{u} : ∀ (A : Type u) [CommRing A], Ideal A → Type (u + 1))
