module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.BaseChange
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.GradedPieces

/-!
# Base change for the graded pieces of projective space

Coefficient homomorphisms act semilinearly on integer homogeneous pieces.  On the dual pieces
appearing in top cohomology, base change is the semilinear extension of the monomial-coordinate
functional.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable {R R' : Type u} [CommRing R] [CommRing R']

/-- Applying a coefficient homomorphism to a polynomial gives a semilinear map between matching
integer homogeneous pieces. -/
def gradedPieceBaseChange (φ : R →+* R') (n : ℕ) (d : ℤ) :
    gradedPiece R n d →ₛₗ[φ] gradedPiece R' n d where
  toFun p :=
    ⟨MvPolynomial.map φ p.1, by
      by_cases hd : 0 ≤ d
      · have hp : p.1 ∈ grading R n d.toNat := by
          rw [← gradedPiece_of_nonneg R n d hd]
          exact p.2
        rw [gradedPiece_of_nonneg R' n d hd]
        exact hp.map φ
      · have hp : p.1 = 0 := by
          have hp' : p.1 ∈ (⊥ : Submodule R (MvPolynomial (Fin (n + 1)) R)) := by
            rw [← gradedPiece_of_neg R n d hd]
            exact p.2
          simpa using hp'
        rw [gradedPiece_of_neg R' n d hd]
        simp [hp]⟩
  map_add' := sorry
  map_smul' := sorry

/-- The semilinear map on an integer homogeneous piece applies the coefficient homomorphism to
the underlying polynomial. -/
@[simp]
theorem gradedPieceBaseChange_apply (φ : R →+* R') (n : ℕ) (d : ℤ)
    (p : gradedPiece R n d) :
    (gradedPieceBaseChange φ n d p : MvPolynomial (Fin (n + 1)) R') =
      MvPolynomial.map φ p.1 := sorry

/-- Base change of a top-cohomology dual extends its values on homogeneous monomials
semilinearly to the target coefficient ring. -/
def topCohomologyDualBaseChange (φ : R →+* R') (n : ℕ) (d : ℤ) :
    topCohomologyDual R n d →ₛₗ[φ] topCohomologyDual R' n d where
  toFun q :=
    { toFun := fun p ↦ p.1.support.attach.sum fun e ↦
        p.1.coeff e.1 * φ
          (q ⟨MvPolynomial.monomial e.1 1,
            by
              let k := -((n : ℤ) + 1) - d
              by_cases hk : 0 ≤ k
              · rw [gradedPiece_of_nonneg R n k hk]
                apply MvPolynomial.isHomogeneous_monomial
                have hp : p.1 ∈ grading R' n k.toNat := by
                  rw [← gradedPiece_of_nonneg R' n k hk]
                  exact p.2
                simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using
                  hp (MvPolynomial.mem_support_iff.mp e.2)
              · rw [gradedPiece_of_neg R n k hk]
                have hp : p.1 = 0 := by
                  have hp' : p.1 ∈
                      (⊥ : Submodule R' (MvPolynomial (Fin (n + 1)) R')) := by
                    rw [← gradedPiece_of_neg R' n k hk]
                    exact p.2
                  simpa using hp'
                exact False.elim (by simpa [hp] using e.2)⟩)
      map_add' := sorry
      map_smul' := sorry }
  map_add' := sorry
  map_smul' := sorry

/-- Evaluation after base change is the monomial-coordinate extension of the original dual
functional. -/
theorem topCohomologyDualBaseChange_apply (φ : R →+* R') (n : ℕ) (d : ℤ)
    (q : topCohomologyDual R n d) (p : gradedPiece R' n (-((n : ℤ) + 1) - d)) :
    topCohomologyDualBaseChange φ n d q p =
      p.1.support.attach.sum fun e ↦
        p.1.coeff e.1 * φ
          (q ⟨MvPolynomial.monomial e.1 1,
            by
              let k := -((n : ℤ) + 1) - d
              by_cases hk : 0 ≤ k
              · rw [gradedPiece_of_nonneg R n k hk]
                apply MvPolynomial.isHomogeneous_monomial
                have hp : p.1 ∈ grading R' n k.toNat := by
                  rw [← gradedPiece_of_nonneg R' n k hk]
                  exact p.2
                simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using
                  hp (MvPolynomial.mem_support_iff.mp e.2)
              · rw [gradedPiece_of_neg R n k hk]
                have hp : p.1 = 0 := by
                  have hp' : p.1 ∈
                      (⊥ : Submodule R' (MvPolynomial (Fin (n + 1)) R')) := by
                    rw [← gradedPiece_of_neg R' n k hk]
                    exact p.2
                  simpa using hp'
                exact False.elim (by simpa [hp] using e.2)⟩) := sorry

end AlgebraicGeometry.ProjectiveSpace
