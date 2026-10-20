module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.FiniteEtaleCompletion
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry IsLocalRing

noncomputable section

universe u

/- Lemma 58.19.4 (1): in Situation 58.19.1, if `(A, (f))` is a henselian pair and
restriction of finite étale covers along `U'_0 → U'` is fully faithful, then
restriction along `U_0 → U` is full. The henselian-pair formulation includes
the henselian local-ring case. -/
@[stacks 0BLI] #check
  (AlgebraicGeometry.PuncturedSpectrum.finiteEtaleBaseChange_full_of_completion :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      (f : maximalIdeal A) [HenselianRing A (principalIdeal f)]
      [(Scheme.finiteEtaleBaseChange
        (AlgebraicGeometry.PuncturedSpectrum.completedPrincipalRestriction f)).Full]
      [(Scheme.finiteEtaleBaseChange
        (AlgebraicGeometry.PuncturedSpectrum.completedPrincipalRestriction f)).Faithful],
      (Scheme.finiteEtaleBaseChange
        (AlgebraicGeometry.PuncturedSpectrum.principalQuotientMap f)).Full)

/- Lemma 58.19.4 (2): in Situation 58.19.1, if `(A, (f))` is a henselian pair and
restriction of finite étale covers along `U'_0 → U'` is fully faithful, then
restriction along `U_0 → U` is faithful. -/
@[stacks 0BLI] #check
  (AlgebraicGeometry.PuncturedSpectrum.finiteEtaleBaseChange_faithful_of_completion :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      (f : maximalIdeal A) [HenselianRing A (principalIdeal f)]
      [(Scheme.finiteEtaleBaseChange
        (AlgebraicGeometry.PuncturedSpectrum.completedPrincipalRestriction f)).Full]
      [(Scheme.finiteEtaleBaseChange
        (AlgebraicGeometry.PuncturedSpectrum.completedPrincipalRestriction f)).Faithful],
      (Scheme.finiteEtaleBaseChange
        (AlgebraicGeometry.PuncturedSpectrum.principalQuotientMap f)).Faithful)
