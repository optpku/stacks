/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Etale.Weakly.IndEtale
import StacksCheckRecall

@[expose] public section

universe u v

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/- Lemma 61.7.6: if a ring map `A → B` is ind-étale, then it is weakly étale
(More on Algebra, Definition 15.105.1). Canonical owner: `Algebra.WeaklyEtale.of_indEtale`. -/
@[stacks 097N] #check (Algebra.WeaklyEtale.of_indEtale :
  (algebraMap A B).IndEtale → Algebra.WeaklyEtale A B)
