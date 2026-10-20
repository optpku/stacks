/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.ThreeEndomorphisms.Determinant

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace CategoryTheory.TwoPeriodicEndomorphism

/- Lemma 42.68.24 (1): the complex on `M` with differentials `alpha` and
`beta.comp gamma` is exact. -/
@[stacks 02PU] #check (CategoryTheory.TwoPeriodicEndomorphism.ofComposite_acyclic :
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [IsLocalRing R] (hM : IsFiniteLength R M) (alpha beta gamma : Module.End R M)
    (hI : ∀ delta₀ delta₁ delta₂,
      List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
        delta₀.range = (delta₁.comp delta₂).ker)
    (hK : ∀ delta₀ delta₁ delta₂,
      List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
        delta₀.ker = (delta₁.comp delta₂).range),
    (ofComposite alpha beta gamma hI hK).toCochainComplex.Acyclic)

/- Lemma 42.68.24 (2): the complex on `range gamma` with the restrictions of
`alpha` and `beta` is exact. -/
@[stacks 02PU] #check (CategoryTheory.TwoPeriodicEndomorphism.onRange_acyclic :
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [IsLocalRing R] (hM : IsFiniteLength R M) (alpha beta gamma : Module.End R M)
    (hI : ∀ delta₀ delta₁ delta₂,
      List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
        delta₀.range = (delta₁.comp delta₂).ker)
    (hK : ∀ delta₀ delta₁ delta₂,
      List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
        delta₀.ker = (delta₁.comp delta₂).range),
    (onRange alpha beta gamma hI hK).toCochainComplex.Acyclic)

/- Lemma 42.68.24 (3): the complex on `M ⧸ ker beta` with the endomorphisms induced
by `alpha` and `gamma` is exact. -/
@[stacks 02PU] #check (CategoryTheory.TwoPeriodicEndomorphism.onKerQuotient_acyclic :
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [IsLocalRing R] (hM : IsFiniteLength R M) (alpha beta gamma : Module.End R M)
    (hI : ∀ delta₀ delta₁ delta₂,
      List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
        delta₀.range = (delta₁.comp delta₂).ker)
    (hK : ∀ delta₀ delta₁ delta₂,
      List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
        delta₀.ker = (delta₁.comp delta₂).range),
    (onKerQuotient alpha beta gamma hI hK).toCochainComplex.Acyclic)

/- Lemma 42.68.24 (4): the periodic determinant on `M` factors as the determinant on
`range gamma` followed by the determinant on `M ⧸ ker beta`. -/
@[stacks 02PU] #check (CategoryTheory.TwoPeriodicEndomorphism.determinant_ofComposite_eq_mul :
  ∀ {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [IsLocalRing R] (hM : IsFiniteLength R M) (alpha beta gamma : Module.End R M)
    (hI : ∀ delta₀ delta₁ delta₂,
      List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
        delta₀.range = (delta₁.comp delta₂).ker)
    (hK : ∀ delta₀ delta₁ delta₂,
      List.Perm [delta₀, delta₁, delta₂] [alpha, beta, gamma] →
        delta₀.ker = (delta₁.comp delta₂).range),
    determinant (ofComposite alpha beta gamma hI hK) hM
        (ofComposite_acyclic hM alpha beta gamma hI hK) =
      determinant (onRange alpha beta gamma hI hK)
          (hM.of_injective gamma.range.subtype_injective)
          (onRange_acyclic hM alpha beta gamma hI hK) *
        determinant (onKerQuotient alpha beta gamma hI hK)
          (hM.of_surjective (Submodule.mkQ_surjective beta.ker))
          (onKerQuotient_acyclic hM alpha beta gamma hI hK))

end CategoryTheory.TwoPeriodicEndomorphism
