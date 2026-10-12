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
# Lemma 33.39.2

The reusable one-dimensional normalization API is owned by `Normalization`.
This chapter entry records its four direct statements.
-/

universe u

/- Lemma 33.39.2 (1): normality of the normalization. -/
@[stacks 0C3S] #check
  (Normalization.isNormalRing_of_reduced_nagataRing_local_dimOne :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R] [NagataRing R] [IsReduced R],
      ringKrullDim R = 1 → IsNormalRing (Normalization.normalizationRing R))

/- Lemma 33.39.2 (2): the Nagata property of the normalization. -/
@[stacks 0C3S] #check
  (Normalization.isNagataRing_of_reduced_nagataRing_local_dimOne :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R] [NagataRing R] [IsReduced R],
      ringKrullDim R = 1 → NagataRing (Normalization.normalizationRing R))

/- Lemma 33.39.2 (3): normalization finiteness. -/
@[stacks 0C3S] #check
  (Normalization.moduleFinite_of_reduced_nagataRing_local_dimOne :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R] [NagataRing R] [IsReduced R],
      ringKrullDim R = 1 → Module.Finite R (Normalization.normalizationRing R))

/- Lemma 33.39.2 (4): finite length of the normalization quotient. -/
@[stacks 0C3S] #check
  (Normalization.quotient_isFiniteLength_of_reduced_nagataRing_local_dimOne :
    ∀ {R : Type u} [CommRing R] [IsLocalRing R] [NagataRing R] [IsReduced R],
      ringKrullDim R = 1 → IsFiniteLength R (Normalization.quotient R))
