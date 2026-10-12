/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.IdealPower.Slice

@[expose] public section

universe u v

#check (Ideal.PowerSlice :
  ∀ {A : Type u} [CommRing A] (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M],
    ℕ → ℕ → Type v)
