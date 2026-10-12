/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.RingTheory.RingHom.IndEtale.Counterexample
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 110.46.1 -/
@[stacks 09AP] #check (RingHom.exists_isIsoOnLocalRings_not_indEtale :
    ∃ (A B : Type u) (_ : CommRing A) (_ : CommRing B) (f : A →+* B),
      f.IsIsoOnLocalRings ∧ ¬ f.IndEtale ∧ ¬ f.IndZariski)
