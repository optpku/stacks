module

public import ReasLib.RingTheory.Normalization.OneDimensional.DeltaInvariant
import StacksCheckRecall

@[expose] public section

open IsLocalRing

universe u v

/- Lemma 33.39.6 (1): The delta invariant is unchanged by henselization. -/
@[stacks 0C3W]
#check (Normalization.OneDimensional.Henselization.deltaInvariant_eq :
  ∀ {A : Type u} {Ah : Type v} [CommRing A] [IsLocalRing A] [NagataRing A]
    [IsReduced A] [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah],
    ringKrullDim A = 1 →
      Normalization.deltaInvariant A = Normalization.deltaInvariant Ah)

/- Lemma 33.39.6 (2): The delta invariant is unchanged by strict henselization. -/
@[stacks 0C3W]
#check (Normalization.OneDimensional.StrictHenselization.deltaInvariant_eq :
  ∀ {A : Type u} {Ash : Type v} [CommRing A] [IsLocalRing A] [NagataRing A]
    [IsReduced A] [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash],
    ringKrullDim A = 1 →
      Normalization.deltaInvariant A = Normalization.deltaInvariant Ash)

/- Lemma 33.39.6 (3): The delta invariant is unchanged by completion. -/
@[stacks 0C3W]
#check (Normalization.OneDimensional.Completion.deltaInvariant_eq :
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [NagataRing A] [IsReduced A],
    ringKrullDim A = 1 → Normalization.deltaInvariant A =
      Normalization.deltaInvariant (AdicCompletion (maximalIdeal A) A))
