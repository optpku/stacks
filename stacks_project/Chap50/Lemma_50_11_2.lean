/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.DifferentialFormCohomology
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 50.11.2 (1): on standard projective `n`-space over `A`, the cohomology of
the sheaf of relative `p`-forms vanishes outside degree `p`, and also when `p > n`. -/
@[stacks 0FUK] #check
  (AlgebraicGeometry.projectiveSpaceDifferentialFormCohomology_isZero :
    ∀ (A : Type u) [CommRing A] (n : ℕ) (_ : 1 ≤ n) (p q : ℕ),
      ¬ (p = q ∧ q ≤ n) →
        IsZero
          (Scheme.Hom.cohomology (ProjectiveSpace.toSpec A n)
            (Λ[p] Ω[(ProjectiveSpace.toSpec A n).toShHom]) q))

/- Lemma 50.11.2 (2): in degrees `p ≤ n`, the `p`th cohomology of the sheaf of
relative `p`-forms on standard projective `n`-space is a free `A`-module of rank one. -/
@[stacks 0FUK] #check
  (AlgebraicGeometry.projectiveSpaceDifferentialFormCohomology_freeRankOne :
    ∀ (A : Type u) [CommRing A] (n : ℕ) (_ : 1 ≤ n) (p : ℕ), p ≤ n →
      CategoryTheory.ModuleCat.freeRankOne A
        (Scheme.Hom.cohomology (ProjectiveSpace.toSpec A n)
          (Λ[p] Ω[(ProjectiveSpace.toSpec A n).toShHom]) p))

/- Lemma 50.11.2 (3): every positive-degree cohomology group of every positive
twist of the sheaf of relative `p`-forms on standard projective `n`-space vanishes. -/
@[stacks 0FUK] #check
  (AlgebraicGeometry.projectiveSpaceTwistedDifferentialFormCohomology_isZero :
    ∀ (A : Type u) [CommRing A] (n : ℕ) (_ : 1 ≤ n) (p q : ℕ) (k : ℤ),
      0 < q → 0 < k →
        IsZero
          (Scheme.Hom.cohomology (ProjectiveSpace.toSpec A n)
            (ProjectiveSpace.twist A n
              (Λ[p] Ω[(ProjectiveSpace.toSpec A n).toShHom]) k) q))
