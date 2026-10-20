/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.PrincipalQuotient
public import stacks_project.Chap58.Lemma_58_5_2
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing

noncomputable section

universe u

/- Lemma 58.19.2 (1): in Situation 58.19.1, if `dim(A/p) ≥ 2` for every
minimal prime `p` of `A` not containing `f`, then restriction of finite étale
covers along the principal quotient map is faithful. -/
@[stacks 0BLG] #check
  (AlgebraicGeometry.PuncturedSpectrum.finiteEtaleBaseChange_faithful_of_minimalPrimeDim :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      (f : maximalIdeal A)
      [Fact (∀ p : PrimeSpectrum A, p.asIdeal ∈ minimalPrimes A →
          (f : A) ∉ p.asIdeal →
            (2 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ p.asIdeal))],
      (Scheme.finiteEtaleBaseChange
        (AlgebraicGeometry.PuncturedSpectrum.principalQuotientMap f)).Faithful)

/- Lemma 58.19.2 (2): in Situation 58.19.1, if every connected component of
the punctured spectrum `U` meets the punctured spectrum `U₀`, then restriction
of finite étale covers along the principal quotient map is faithful. -/
@[stacks 0BLG] #check
  (AlgebraicGeometry.PuncturedSpectrum.finiteEtaleBaseChange_faithful_of_meetsConnectedComponents :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
      (f : maximalIdeal A)
      [Fact (∀ x : AlgebraicGeometry.PuncturedSpectrum.scheme A,
          ∃ y : @AlgebraicGeometry.PuncturedSpectrum.scheme
              (A ⧸ principalIdeal (f : A)) _
              (IsLocalRing.quotientSpanSingleton f),
            AlgebraicGeometry.PuncturedSpectrum.principalQuotientMap f y ∈
              connectedComponent x)],
      (Scheme.finiteEtaleBaseChange
        (AlgebraicGeometry.PuncturedSpectrum.principalQuotientMap f)).Faithful)
