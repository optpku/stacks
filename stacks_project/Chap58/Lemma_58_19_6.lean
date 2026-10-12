/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.FiniteEtale
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry IsLocalRing

noncomputable section

universe u

/- Lemma 58.19.6 (1): in Situation 58.19.1, if a power of `f` annihilates
`H¹_𝔪(A)` and `H²_𝔪(A)` and `(A, (f))` is a henselian pair, then restriction
`FÉt_U ⟶ FÉt_{U₀}` along `principalQuotientMap f` is full. -/
@[stacks 0BM6] #check
  (AlgebraicGeometry.PuncturedSpectrum.finiteEtaleBaseChange_full_of_localCohomology :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      (f : maximalIdeal A)
      [HenselianRing A (principalIdeal f)]
      [Fact (Module.IsAnnihilatedByPower (Ideal.span ({(f : A)} : Set A))
        ((localCohomology (maximalIdeal A) 1).obj (ModuleCat.of A A)))]
      [Fact (Module.IsAnnihilatedByPower (Ideal.span ({(f : A)} : Set A))
        ((localCohomology (maximalIdeal A) 2).obj (ModuleCat.of A A)))],
      (Scheme.finiteEtaleBaseChange
        (AlgebraicGeometry.PuncturedSpectrum.principalQuotientMap f)).Full)

/- Lemma 58.19.6 (2): in Situation 58.19.1, if a power of `f` annihilates
`H¹_𝔪(A)` and `H²_𝔪(A)` and `(A, (f))` is a henselian pair, then restriction
`FÉt_U ⟶ FÉt_{U₀}` along `principalQuotientMap f` is faithful. -/
@[stacks 0BM6] #check
  (AlgebraicGeometry.PuncturedSpectrum.finiteEtaleBaseChange_faithful_of_localCohomology :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      (f : maximalIdeal A)
      [HenselianRing A (principalIdeal f)]
      [Fact (Module.IsAnnihilatedByPower (Ideal.span ({(f : A)} : Set A))
        ((localCohomology (maximalIdeal A) 1).obj (ModuleCat.of A A)))]
      [Fact (Module.IsAnnihilatedByPower (Ideal.span ({(f : A)} : Set A))
        ((localCohomology (maximalIdeal A) 2).obj (ModuleCat.of A A)))],
      (Scheme.finiteEtaleBaseChange
        (AlgebraicGeometry.PuncturedSpectrum.principalQuotientMap f)).Faithful)
