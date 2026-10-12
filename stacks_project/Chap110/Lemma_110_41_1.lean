/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Smooth.Counterexample.NonFlat
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 110.41.1 -/
@[stacks 057W]
#check (RingHom.exists_formallySmooth_not_flat :
  ∃ (R S : Type u) (_ : CommRing R) (_ : CommRing S) (f : R →+* S),
    f.FormallySmooth ∧ ¬ f.Flat)
