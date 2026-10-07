module

public import stacks_project.Chap27.Lemma_27_13_8_Reconstruction

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.TwistedSections

/-- Lemma 27.13.8 (1): the carrier of the graded `R[T₀, …, Tₙ]`-module of
nonnegative twisted sections is `⨁ d : ℕ, Γ(F(d))`. -/
@[stacks 03GM]
theorem gradedModule_carrier_eq_twistedSections
    {R : Type u} [CommRing R] {n : ℕ}
    (P : ProjTwistPresentation (ProjectiveSpace.grading R n))
    (T : ProjTwistMulPresentation (ProjectiveSpace.grading R n) P)
    (F : Scheme.QCoh (ProjectiveSpace.scheme R n)) :
    (gradedModule P T F : Type u) = twistedSections P F := sorry

end AlgebraicGeometry.ProjectiveSpace.TwistedSections
