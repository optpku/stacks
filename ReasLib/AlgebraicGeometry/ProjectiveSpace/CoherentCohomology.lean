/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Twist
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.CoherentCohomology
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cohomology.Map

/-!
# Cohomology of coherent sheaves on standard projective space

This file records finiteness and vanishing results for coherent sheaves and their twists on
standard projective space over a Noetherian ring.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] [IsNoetherianRing R] (n : ℕ)
variable (ℱ : (scheme R n).Modules) [ℱ.IsCoherent]

namespace Coherent

/-- Every coherent sheaf on standard projective space is a quotient of a finite coproduct of
canonical twisting sheaves. -/
@[stacks 01YS "finite presentation of a coherent sheaf by twists"]
theorem exists_epi_from_twists :
    ∃ (r : ℕ) (d : Fin r → ℤ)
      (π : (∐ fun j : Fin r ↦ twistingSheaf R n (d j)) ⟶ ℱ), Epi π := sorry

/-- Cohomology of a coherent sheaf on standard projective `n`-space vanishes in degrees
strictly greater than `n`. -/
@[stacks 01YS "coherent cohomology vanishes above projective dimension"]
theorem cohomology_isZero_of_dimension_lt
    (i : ℕ) (hi : n < i) :
    IsZero (Scheme.Hom.cohomology (toSpec R n) ℱ i) := sorry

/-- The cohomology of a coherent sheaf on standard projective space is finite over the base
ring in every degree. -/
@[stacks 01YS "finiteness of coherent cohomology on projective space"]
theorem cohomology_finite (i : ℕ) :
    Module.Finite R (Scheme.Hom.cohomology (toSpec R n) ℱ i) := sorry

/-- Positive-degree cohomology of a coherent sheaf twisted by sufficiently large canonical
twisting sheaves vanishes. -/
@[stacks 01YS "eventual vanishing of positive coherent twist cohomology"]
theorem twistCohomology_eventually_isZero
    (i : ℕ) (hi : 0 < i) :
    ∃ b : ℤ, ∀ d : ℤ, b ≤ d →
      IsZero (Scheme.Hom.cohomology (toSpec R n) (twist R n ℱ d) i) := sorry

/-- Every truncation of the canonically graded global sections of the twists of a coherent
sheaf is finite over the homogeneous coordinate ring. -/
@[stacks 01YS "finiteness of truncated coherent twist sections"]
theorem truncatedSections_finite
    (k : ℤ) :
    Module.Finite (MvPolynomial (Fin (n + 1)) R)
      (Proj.TwistedSections.Cohomology.truncated (grading R n) ℱ k) := sorry

end Coherent

end AlgebraicGeometry.ProjectiveSpace
