/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.PuncturedSpectrum.Affine
import ReasLib.AlgebraicGeometry.PuncturedSpectrum.LocalCohomology

universe u v

/- Remark 31.16.3 (1): an affine punctured spectrum gives a finitely generated ideal whose
radical is the maximal ideal. -/
@[stacks 0BCT] #check
  (AlgebraicGeometry.PuncturedSpectrum.exists_fg_maximalIdeal_eq_radical_of_isAffineOpen :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A],
      AlgebraicGeometry.IsAffineOpen (AlgebraicGeometry.PuncturedSpectrum.puncturedOpen A) →
        ∃ I : Ideal A, I.FG ∧ IsLocalRing.maximalIdeal A = I.radical)

/- Remark 31.16.3 (2): a principal ideal whose radical is the maximal ideal gives an affine
punctured spectrum. -/
@[stacks 0BCT] #check
  (AlgebraicGeometry.PuncturedSpectrum.isAffineOpen_of_maximalIdeal_eq_radical_span_singleton :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A] {f : A},
      IsLocalRing.maximalIdeal A = (Ideal.span ({f} : Set A)).radical →
        AlgebraicGeometry.IsAffineOpen (AlgebraicGeometry.PuncturedSpectrum.puncturedOpen A))

/- Remark 31.16.3 (3): after quotienting by a nonzerodivisor in the maximal ideal, degree-zero
local cohomology supported on the chosen finitely generated ideal does not vanish. -/
@[stacks 0BCT] #check
  (AlgebraicGeometry.PuncturedSpectrum.not_isZero_localCohomology_zero_quotient_of_isAffineOpen :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A],
      AlgebraicGeometry.IsAffineOpen (AlgebraicGeometry.PuncturedSpectrum.puncturedOpen A) →
        ∀ {I : Ideal A}, I.FG → IsLocalRing.maximalIdeal A = I.radical →
          ∀ {f : A}, f ∈ IsLocalRing.maximalIdeal A → f ∈ nonZeroDivisors A →
            ¬ CategoryTheory.Limits.IsZero ((localCohomology I 0).obj
              (ModuleCat.of A (A ⧸ Ideal.span ({f} : Set A)))))

/- Remark 31.16.3 (4): the local-cohomology obstruction persists over a local homomorphism
with the prescribed radical condition, using the extension of the chosen ideal as support. -/
@[stacks 0BCT] #check
  (AlgebraicGeometry.PuncturedSpectrum.not_isZero_localCohomology_zero_quotient_of_localHom :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A],
      AlgebraicGeometry.IsAffineOpen (AlgebraicGeometry.PuncturedSpectrum.puncturedOpen A) →
        ∀ {I : Ideal A}, I.FG → IsLocalRing.maximalIdeal A = I.radical →
          ∀ {A' : Type v} [CommRing A'] [IsLocalRing A'],
            ∀ (φ : A →+* A') [IsLocalHom φ],
              IsLocalRing.maximalIdeal A' =
                  (Ideal.map φ (IsLocalRing.maximalIdeal A)).radical →
                ∀ {f : A'}, f ∈ IsLocalRing.maximalIdeal A' → f ∈ nonZeroDivisors A' →
                  ¬ CategoryTheory.Limits.IsZero ((localCohomology (Ideal.map φ I) 0).obj
                    (ModuleCat.of A' (A' ⧸ Ideal.span ({f} : Set A')))))

/- Remark 31.16.3 (5): an affine punctured spectrum rules out regular sequences of length two
in the local ring. -/
@[stacks 0BCT] #check
  (AlgebraicGeometry.PuncturedSpectrum.not_isRegular_pair_of_isAffineOpen :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A],
      AlgebraicGeometry.IsAffineOpen (AlgebraicGeometry.PuncturedSpectrum.puncturedOpen A) →
        ∀ f g : A, ¬ RingTheory.Sequence.IsRegular A [f, g])

/- Remark 31.16.3 (6): the same regular-pair obstruction holds in a local target with the
prescribed radical condition. -/
@[stacks 0BCT] #check
  (AlgebraicGeometry.PuncturedSpectrum.not_isRegular_pair_of_localHom :
    ∀ {A : Type u} [CommRing A] [IsLocalRing A],
      AlgebraicGeometry.IsAffineOpen (AlgebraicGeometry.PuncturedSpectrum.puncturedOpen A) →
        ∀ {A' : Type v} [CommRing A'] [IsLocalRing A'],
          ∀ (φ : A →+* A') [IsLocalHom φ],
            IsLocalRing.maximalIdeal A' =
                (Ideal.map φ (IsLocalRing.maximalIdeal A)).radical →
              ∀ f g : A', ¬ RingTheory.Sequence.IsRegular A' [f, g])
