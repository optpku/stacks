module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.FiniteEtaleDepth
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry IsLocalRing

noncomputable section

universe u

/- Lemma 58.19.7 (1): in Situation 58.19.1, if `depth(A) ≥ 3` and `(A, (f))` is
a henselian pair (in particular if `A` is henselian), then restriction
`FÉt_U ⟶ FÉt_{U₀}` along `principalQuotientMap f` is full. -/
@[stacks 0BLJ] #check
  (AlgebraicGeometry.PuncturedSpectrum.finiteEtaleBaseChange_full_of_depth :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      (f : maximalIdeal A)
      [HenselianRing A (principalIdeal f)]
      [Fact ((3 : ℕ∞) ≤ moduleDepth A A)],
      (Scheme.finiteEtaleBaseChange
        (AlgebraicGeometry.PuncturedSpectrum.principalQuotientMap f)).Full)

/- Lemma 58.19.7 (2): in Situation 58.19.1, if `depth(A) ≥ 3` and `(A, (f))` is
a henselian pair (in particular if `A` is henselian), then restriction
`FÉt_U ⟶ FÉt_{U₀}` along `principalQuotientMap f` is faithful. -/
@[stacks 0BLJ] #check
  (AlgebraicGeometry.PuncturedSpectrum.finiteEtaleBaseChange_faithful_of_depth :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      (f : maximalIdeal A)
      [HenselianRing A (principalIdeal f)]
      [Fact ((3 : ℕ∞) ≤ moduleDepth A A)],
      (Scheme.finiteEtaleBaseChange
        (AlgebraicGeometry.PuncturedSpectrum.principalQuotientMap f)).Faithful)
