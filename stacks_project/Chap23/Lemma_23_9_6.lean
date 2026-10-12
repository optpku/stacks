/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.CompleteIntersection.Local.TorDimension

@[expose] public section

universe u v

open PrimeSpectrum Set

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/- Lemma 23.9.6 (tag `09QF`): for a finite-type map from a Noetherian
ring whose spectrum image contains every closed point, the target-LCI plus
finite-Tor condition is equivalent to the source-LCI plus relative-LCI
condition. -/
@[stacks 09QF]
#check (RingHom.CompleteIntersection.FiniteTorDimension.target_iff_source :
  ∀ (f : A →+* B) [IsNoetherianRing A], f.FiniteType →
    (closedPoints (PrimeSpectrum A) ⊆ Set.range (PrimeSpectrum.comap f) →
      ((IsLocalCompleteIntersectionRing B ∧ f.HasFiniteTorDimension) ↔
        (IsLocalCompleteIntersectionRing A ∧ f.IsLocalCompleteIntersection))))
