/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Proper
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Twist.Coherent
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.CoherentCohomology
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.Presentation
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.EulerCharacteristic
public import ReasLib.RingTheory.Polynomial.Numerical

/-!
# Hilbert polynomials on standard projective space

This file defines the Euler-characteristic function of the canonical twists of
a coherent module on standard projective space. It also records the analogous
function determined by an explicit projective-spectrum twist presentation.
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- The Hilbert polynomial of a coherent module on standard projective space is the Euler
characteristic of each of its canonical integral twists. -/
noncomputable def hilbertPolynomial
    (k : Type u) [Field k] (n : ℕ)
    (ℱ : (scheme k n).Modules) [ℱ.IsCoherent] : ℤ → ℤ :=
  fun d ↦ Scheme.Hom.eulerCharacteristic (toSpec k n) (twist k n ℱ d)

/-- Evaluating the Hilbert polynomial at `d` gives the Euler characteristic of the degree-`d`
twist. -/
theorem hilbertPolynomial_apply
    (k : Type u) [Field k] (n : ℕ)
    (ℱ : (scheme k n).Modules) [ℱ.IsCoherent] (d : ℤ) :
    hilbertPolynomial k n ℱ d =
      Scheme.Hom.eulerCharacteristic (toSpec k n) (twist k n ℱ d) := sorry

/-- The Euler-characteristic function of the canonical twists of a coherent module on standard
projective space is a numerical polynomial. -/
theorem hilbertPolynomial_isNumericalPolynomial
    (k : Type u) [Field k] (n : ℕ)
    (ℱ : (scheme k n).Modules) [ℱ.IsCoherent] :
    IsNumericalPolynomial (hilbertPolynomial k n ℱ) := sorry

/-- A rational polynomial is a Hilbert polynomial of a coherent module on standard projective
space when its values at integers equal the Euler characteristics of the canonical twists. -/
def IsHilbertPolynomial
    (k : Type u) [Field k] (n : ℕ)
    (ℱ : (scheme k n).Modules) [ℱ.IsCoherent] (P : Polynomial ℚ) : Prop :=
  ∀ d : ℤ, P.eval (d : ℚ) = (hilbertPolynomial k n ℱ d : ℚ)

/-- The Euler characteristics of all integral twists of a coherent sheaf on projective space
over a field are the values of a rational polynomial. -/
theorem exists_isHilbertPolynomial
    (k : Type u) [Field k] (n : ℕ)
    (ℱ : (scheme k n).Modules) [ℱ.IsCoherent] :
    ∃ P : Polynomial ℚ, IsHilbertPolynomial k n ℱ P := sorry

namespace IsHilbertPolynomial

/-- In sufficiently large degree, a Hilbert polynomial of a coherent module on standard
projective space equals the dimension of the zeroth cohomology of its canonical twist. -/
theorem eventually_eq_finrank_cohomologyZero
    (k : Type u) [Field k] (n : ℕ)
    (ℱ : (scheme k n).Modules) [ℱ.IsCoherent]
    (P : Polynomial ℚ) (hP : IsHilbertPolynomial k n ℱ P) :
    ∃ b : ℤ, ∀ d : ℤ, b ≤ d →
      P.eval (d : ℚ) =
        (Scheme.Hom.cohomologyFinrank (toSpec k n) (twist k n ℱ d) 0 : ℚ) := sorry

end IsHilbertPolynomial

end AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry

/-- The signed cohomology-dimension function determined by an explicit twist presentation on
standard projective space. -/
noncomputable def projectiveSpaceHilbertPolynomial
    (k : Type u) [Field k] (n : ℕ)
    (P : ProjTwistPresentation (ProjectiveSpace.grading k n))
    (ℱ : (ProjectiveSpace.scheme k n).Modules) [ℱ.IsCoherent] : ℤ → ℤ :=
  fun d ↦
    ∑ᶠ i : ℕ,
      (((i : ℤ).negOnePow : ℤ) *
        Int.ofNat
          (Scheme.Hom.cohomologyFinrank (ProjectiveSpace.toSpec k n)
            (P.tensorTwist ℱ d) i))

/-- The presentation-dependent Hilbert function unfolds as the signed finite sum of the
dimensions of the cohomology of the presented twists. -/
theorem projectiveSpaceHilbertPolynomial_spec
    (k : Type u) [Field k] (n : ℕ)
    (P : ProjTwistPresentation (ProjectiveSpace.grading k n))
    (ℱ : (ProjectiveSpace.scheme k n).Modules) [ℱ.IsCoherent] (d : ℤ) :
    projectiveSpaceHilbertPolynomial k n P ℱ d =
      ∑ᶠ i : ℕ,
        (((i : ℤ).negOnePow : ℤ) *
          Int.ofNat
            (Scheme.Hom.cohomologyFinrank (ProjectiveSpace.toSpec k n)
              (P.tensorTwist ℱ d) i)) := sorry

end AlgebraicGeometry
