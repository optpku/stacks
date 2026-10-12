/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Module.Injective
public import Mathlib.RingTheory.Noetherian.Defs

@[expose] public section

universe u v w

/-- Direct sums of injective modules over a Noetherian commutative ring are injective. -/
instance Module.Injective.directSum
    (R : Type u) [CommRing R] [IsNoetherianRing R] {ι : Type v} (E : ι → Type w)
    [Small.{w} R] [∀ i, AddCommGroup (E i)] [∀ i, Module R (E i)]
    [∀ i, Module.Injective R (E i)] : Module.Injective R (DirectSum ι E) := sorry
