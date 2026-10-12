/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.IndEtaleEnvelope.Iteration

@[expose] public section

universe u

/- Lemma 61.8.1: the sequential colimit of the iterated ind-étale envelopes. -/
#check (Algebra.IndEtaleEnvelope.Iteration : ∀ (A : Type u) [CommRing A], Type u)

#check (Algebra.IndEtaleEnvelope.iterate : ∀ (A : Type u) [CommRing A], ℕ → Type u)

#check (Algebra.IndEtaleEnvelope.ι : ∀ (A : Type u) [CommRing A] (n : ℕ),
  Algebra.IndEtaleEnvelope.iterate A n →+* Algebra.IndEtaleEnvelope.Iteration A)

#check (Algebra.IndEtaleEnvelope.algebraMap_iteration : ∀ (A : Type u) [CommRing A],
  A →+* Algebra.IndEtaleEnvelope.Iteration A)
