/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Etale.Counterexample.NonFlat
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 110.42.1: there exist formally étale nonflat ring maps. -/
@[stacks 060I] #check (RingHom.exists_formallyEtale_not_flat :
  ∃ (R S : Type u) (_ : CommRing R) (_ : CommRing S) (f : R →+* S),
    f.FormallyEtale ∧ ¬ f.Flat)
