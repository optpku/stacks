/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Normalization.OneDimensional.BaseChange
import StacksCheckRecall

@[expose] public section

open IsLocalRing
open scoped TensorProduct

universe u v

/- Lemma 33.39.5 (1): a henselization of a reduced one-dimensional Nagata local ring is
reduced. -/
@[stacks 0C3V] #check (Normalization.OneDimensional.Henselization.isReduced :
  ∀ {A : Type u} {Ah : Type v} [CommRing A] [IsLocalRing A] [NagataRing A] [IsReduced A]
    [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah],
    ringKrullDim A = 1 → IsReduced Ah)

/- Lemma 33.39.5 (2): a henselization of a reduced one-dimensional Nagata local ring is
Nagata. -/
@[stacks 0C3V] #check (Normalization.OneDimensional.Henselization.isNagataRing :
  ∀ {A : Type u} {Ah : Type v} [CommRing A] [IsLocalRing A] [NagataRing A] [IsReduced A]
    [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah],
    ringKrullDim A = 1 → NagataRing Ah)

/- Lemma 33.39.5 (3): a henselization of a reduced one-dimensional Nagata local ring has
Krull dimension one. -/
@[stacks 0C3V] #check (Normalization.OneDimensional.Henselization.krullDim_eq_one :
  ∀ {A : Type u} {Ah : Type v} [CommRing A] [IsLocalRing A] [NagataRing A] [IsReduced A]
    [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah],
    ringKrullDim A = 1 → ringKrullDim Ah = 1)

/- Lemma 33.39.5 (4): the normalization tensor base change to a henselization is its integral
closure in the total quotient ring. -/
@[stacks 0C3V] #check (Normalization.OneDimensional.Henselization.isIntegralClosure :
  ∀ {A : Type u} {Ah : Type v} [CommRing A] [IsLocalRing A] [NagataRing A] [IsReduced A]
    [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah],
    ringKrullDim A = 1 →
      let _ : Algebra (Normalization.normalizationRing A ⊗[A] Ah)
          (Localization.totalQuotientRing Ah) :=
        Normalization.BaseChange.Henselization.algebra
      IsIntegralClosure (Normalization.normalizationRing A ⊗[A] Ah) Ah
        (Localization.totalQuotientRing Ah))

/- Lemma 33.39.5 (5): a strict henselization of a reduced one-dimensional Nagata local ring is
reduced. -/
@[stacks 0C3V] #check (Normalization.OneDimensional.StrictHenselization.isReduced :
  ∀ {A : Type u} {Ash : Type v} [CommRing A] [IsLocalRing A] [NagataRing A] [IsReduced A]
    [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash],
    ringKrullDim A = 1 → IsReduced Ash)

/- Lemma 33.39.5 (6): a strict henselization of a reduced one-dimensional Nagata local ring is
Nagata. -/
@[stacks 0C3V] #check (Normalization.OneDimensional.StrictHenselization.isNagataRing :
  ∀ {A : Type u} {Ash : Type v} [CommRing A] [IsLocalRing A] [NagataRing A] [IsReduced A]
    [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash],
    ringKrullDim A = 1 → NagataRing Ash)

/- Lemma 33.39.5 (7): a strict henselization of a reduced one-dimensional Nagata local ring has
Krull dimension one. -/
@[stacks 0C3V] #check (Normalization.OneDimensional.StrictHenselization.krullDim_eq_one :
  ∀ {A : Type u} {Ash : Type v} [CommRing A] [IsLocalRing A] [NagataRing A] [IsReduced A]
    [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash],
    ringKrullDim A = 1 → ringKrullDim Ash = 1)

/- Lemma 33.39.5 (8): the normalization tensor base change to a strict henselization is its
integral closure in the total quotient ring. -/
@[stacks 0C3V] #check (Normalization.OneDimensional.StrictHenselization.isIntegralClosure :
  ∀ {A : Type u} {Ash : Type v} [CommRing A] [IsLocalRing A] [NagataRing A] [IsReduced A]
    [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash],
    ringKrullDim A = 1 →
      let _ : Algebra (Normalization.normalizationRing A ⊗[A] Ash)
          (Localization.totalQuotientRing Ash) :=
        Normalization.BaseChange.StrictHenselization.algebra
          (IsStrictHenselizationOf.rawIndEtale (R := A) (S := Ash))
      IsIntegralClosure (Normalization.normalizationRing A ⊗[A] Ash) Ash
        (Localization.totalQuotientRing Ash))

/- Lemma 33.39.5 (9): the maximal-ideal completion of a reduced one-dimensional Nagata local
ring is local. -/
@[stacks 0C3V] #check (Normalization.OneDimensional.Completion.isLocalRing :
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [NagataRing A] [IsReduced A],
    ringKrullDim A = 1 → IsLocalRing (AdicCompletion (maximalIdeal A) A))

/- Lemma 33.39.5 (10): the maximal-ideal completion of a reduced one-dimensional Nagata local
ring is reduced. -/
@[stacks 0C3V] #check (Normalization.OneDimensional.Completion.isReduced :
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [NagataRing A] [IsReduced A],
    ringKrullDim A = 1 → IsReduced (AdicCompletion (maximalIdeal A) A))

/- Lemma 33.39.5 (11): the maximal-ideal completion of a reduced one-dimensional Nagata local
ring is Nagata. -/
@[stacks 0C3V] #check (Normalization.OneDimensional.Completion.isNagataRing :
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [NagataRing A] [IsReduced A],
    ringKrullDim A = 1 → NagataRing (AdicCompletion (maximalIdeal A) A))

/- Lemma 33.39.5 (12): the maximal-ideal completion of a reduced one-dimensional Nagata local
ring has Krull dimension one. -/
@[stacks 0C3V] #check (Normalization.OneDimensional.Completion.krullDim_eq_one :
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [NagataRing A] [IsReduced A],
    ringKrullDim A = 1 → ringKrullDim (AdicCompletion (maximalIdeal A) A) = 1)

/- Lemma 33.39.5 (13): the normalization tensor base change to the maximal-ideal completion is
its integral closure in the total quotient ring. -/
@[stacks 0C3V] #check (Normalization.OneDimensional.Completion.isIntegralClosure :
  ∀ {A : Type u} [CommRing A] [IsLocalRing A] [NagataRing A] [IsReduced A],
    ringKrullDim A = 1 →
      let _ : Algebra
          (Normalization.normalizationRing A ⊗[A] AdicCompletion (maximalIdeal A) A)
          (Localization.totalQuotientRing (AdicCompletion (maximalIdeal A) A)) :=
        Normalization.BaseChange.Completion.algebra
      IsIntegralClosure
        (Normalization.normalizationRing A ⊗[A] AdicCompletion (maximalIdeal A) A)
        (AdicCompletion (maximalIdeal A) A)
        (Localization.totalQuotientRing (AdicCompletion (maximalIdeal A) A)))
