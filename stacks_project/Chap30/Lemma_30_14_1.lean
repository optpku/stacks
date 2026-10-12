/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.ProjectiveSpace.CoherentCohomology

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped DirectSum

noncomputable section

universe u

/- Lemma 30.14.1 (1) -/
@[stacks 01YS] #check
  (AlgebraicGeometry.ProjectiveSpace.Coherent.exists_epi_from_twists :
    ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (n : ℕ)
      (ℱ : (AlgebraicGeometry.ProjectiveSpace.scheme R n).Modules) [ℱ.IsCoherent],
      ∃ (r : ℕ) (d : Fin r → ℤ)
        (π : (∐ fun j : Fin r ↦
          AlgebraicGeometry.ProjectiveSpace.twistingSheaf R n (d j)) ⟶ ℱ), Epi π)

/- Lemma 30.14.1 (2) -/
@[stacks 01YS] #check
  (AlgebraicGeometry.ProjectiveSpace.Coherent.cohomology_isZero_of_dimension_lt :
    ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (n : ℕ)
      (ℱ : (AlgebraicGeometry.ProjectiveSpace.scheme R n).Modules) [ℱ.IsCoherent]
      (i : ℕ), n < i →
      IsZero (AlgebraicGeometry.Scheme.Hom.cohomology
        (AlgebraicGeometry.ProjectiveSpace.toSpec R n) ℱ i))

/- Lemma 30.14.1 (3) -/
@[stacks 01YS] #check
  (AlgebraicGeometry.ProjectiveSpace.Coherent.cohomology_finite :
    ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (n : ℕ)
      (ℱ : (AlgebraicGeometry.ProjectiveSpace.scheme R n).Modules) [ℱ.IsCoherent]
      (i : ℕ),
      Module.Finite R (AlgebraicGeometry.Scheme.Hom.cohomology
        (AlgebraicGeometry.ProjectiveSpace.toSpec R n) ℱ i))

/- Lemma 30.14.1 (4) -/
@[stacks 01YS] #check
  (AlgebraicGeometry.ProjectiveSpace.Coherent.twistCohomology_eventually_isZero :
    ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (n : ℕ)
      (ℱ : (AlgebraicGeometry.ProjectiveSpace.scheme R n).Modules) [ℱ.IsCoherent]
      (i : ℕ), 0 < i →
      ∃ b : ℤ, ∀ d : ℤ, b ≤ d →
        IsZero (AlgebraicGeometry.Scheme.Hom.cohomology
          (AlgebraicGeometry.ProjectiveSpace.toSpec R n)
          (AlgebraicGeometry.ProjectiveSpace.twist R n ℱ d) i))

/- Lemma 30.14.1 (5) -/
@[stacks 01YS] #check
  (AlgebraicGeometry.ProjectiveSpace.Coherent.truncatedSections_finite :
    ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (n : ℕ)
      (ℱ : (AlgebraicGeometry.ProjectiveSpace.scheme R n).Modules) [ℱ.IsCoherent]
      (k : ℤ),
      Module.Finite (MvPolynomial (Fin (n + 1)) R)
        (AlgebraicGeometry.Proj.TwistedSections.Cohomology.truncated
          (AlgebraicGeometry.ProjectiveSpace.grading R n) ℱ k))
