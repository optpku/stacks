/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Normalization.OneDimensional
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 33.39.4 Source Bridge

The vanishing criterion is owned by the shared one-dimensional normalization
API and is checked directly here.
-/

universe u

/- Lemma 33.39.4: the discrete-valuation-ring criterion. -/
@[stacks 0C3U] #check (Normalization.deltaInvariant_eq_zero_iff_isDiscreteValuationRing : ∀ {R : Type u} [CommRing R] [IsLocalRing R] [NagataRing R] [IsReduced R], ringKrullDim R = 1 → (Normalization.deltaInvariant R = 0 ↔ ∃ (h_domain : IsDomain R), IsDiscreteValuationRing R))
