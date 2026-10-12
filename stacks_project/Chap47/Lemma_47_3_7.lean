/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Injective.DirectSum
import StacksCheckRecall

@[expose] public section

universe u v w

/- Lemma 47.3.7: A direct sum of injective modules over a Noetherian ring is injective. -/
@[stacks 08XV] #check
  (Module.Injective.directSum :
    ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] {ι : Type v} (E : ι → Type w)
      [Small.{w} R] [∀ i, AddCommGroup (E i)] [∀ i, Module R (E i)]
      [∀ i, Module.Injective R (E i)], Module.Injective R (DirectSum ι E))
