/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
import StacksCheckRecall

@[expose] public section

universe u v

open ProjectiveSpectrum AlgebraicGeometry

section

variable {A : Type u} {σ : Type v}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/- Exercise 111.27.4 (1): `D₊(f)` is the open set `basicOpen 𝒜 f` in
`ProjectiveSpectrum 𝒜`. -/
@[stacks 02E9] #check @ProjectiveSpectrum.isOpen_basicOpen

/- Exercise 111.27.4 (2): `D₊(f * f') = D₊(f) ∩ D₊(f')` is `basicOpen_mul`. -/
@[stacks 02E9] #check @ProjectiveSpectrum.basicOpen_mul

namespace ProjectiveSpectrum

/-- Exercise 111.27.4 (3): identifying `D(g) ∩ Proj` with `basicOpen 𝒜 g`, this equals the
union of `D(g₀) ∩ Proj` and the positive-degree standard opens `D₊(gᵢ)` for the homogeneous
components `gᵢ = GradedRing.proj 𝒜 i g`. -/
@[stacks 02E9]
theorem basicOpen_eq_projZero_sup_iSup_pos (g : A) :
    basicOpen 𝒜 g =
      basicOpen 𝒜 (GradedRing.proj 𝒜 0 g) ⊔
        ⨆ i : {n : ℕ // 1 ≤ n}, basicOpen 𝒜 (GradedRing.proj 𝒜 i.1 g) :=
  sorry

/-- Membership form of `basicOpen_eq_projZero_sup_iSup_pos`. -/
theorem mem_basicOpen_eq_projZero_sup_iSup_pos (g : A) (x : ProjectiveSpectrum 𝒜) :
    x ∈ basicOpen 𝒜 g ↔
      x ∈ basicOpen 𝒜 (GradedRing.proj 𝒜 0 g) ∨
        ∃ i : {n : ℕ // 1 ≤ n}, x ∈ basicOpen 𝒜 (GradedRing.proj 𝒜 i.1 g) :=
  sorry

/-- Exercise 111.27.4 (4): if `g₀` is homogeneous of degree 0, then `D(g₀) ∩ Proj` is the union
of the positive-degree standard opens `D₊(g₀ * f)` as `f` runs over homogeneous elements of
positive degree. -/
@[stacks 02E9]
theorem basicOpen_degreeZero_eq_iSup_mul (g₀ : 𝒜 0) :
    basicOpen 𝒜 (g₀ : A) =
      ⨆ d : {n : ℕ // 0 < n}, ⨆ f : 𝒜 d.1,
        basicOpen 𝒜 ((g₀ : A) * (f : A)) :=
  sorry

/-- Membership form of `basicOpen_degreeZero_eq_iSup_mul`. -/
theorem mem_basicOpen_degreeZero_iff (g₀ : 𝒜 0) (x : ProjectiveSpectrum 𝒜) :
    x ∈ basicOpen 𝒜 (g₀ : A) ↔
      ∃ d : ℕ, ∃ f : 𝒜 d, 0 < d ∧ x ∈ basicOpen 𝒜 ((g₀ : A) * (f : A)) :=
  sorry

end ProjectiveSpectrum

/- Exercise 111.27.4 (5): the collection `{D₊(f)}` is a topological basis of
`ProjectiveSpectrum 𝒜`. -/
@[stacks 02E9] #check @ProjectiveSpectrum.isTopologicalBasis_basic_opens

/- Exercise 111.27.4 (6): for homogeneous `f ∈ 𝒜 m` of positive degree, there is a canonical
bijection `D₊(f) → Spec(HomogeneousLocalization.Away 𝒜 f)`. -/
@[stacks 02E9] #check @AlgebraicGeometry.ProjIsoSpecTopComponent.toSpec_bijective

/- Exercise 111.27.4 (7): the bijection of (6) is a homeomorphism. -/
@[stacks 02E9] #check @AlgebraicGeometry.projIsoSpecTopComponent

end

/-- The standard total-degree grading on `MvPolynomial ℕ ℤ`. -/
noncomputable instance instGradedAlgebraMvPolynomialNatInt :
    GradedAlgebra (MvPolynomial.homogeneousSubmodule ℕ ℤ) :=
  MvPolynomial.gradedAlgebra

/-- Exercise 111.27.4 (8): the projective spectrum of the standard-graded polynomial ring
`MvPolynomial ℕ ℤ` is not quasi-compact. -/
@[stacks 02E9]
theorem not_isCompactSpace_projectiveSpectrum_mvPolynomial_nat_int :
    ¬ CompactSpace (ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule ℕ ℤ)) :=
  sorry

section

variable {A : Type u} {σ : Type v}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

namespace ProjectiveSpectrum

/-- Exercise 111.27.4 (9): every closed subset `T` of `ProjectiveSpectrum 𝒜` equals `V₊(I)` for
the homogeneous ideal `I = vanishingIdeal T`. -/
@[stacks 02E9]
theorem eq_zeroLocus_vanishingIdeal_of_isClosed (T : Set (ProjectiveSpectrum 𝒜))
    (hT : IsClosed T) : T = zeroLocus 𝒜 (vanishingIdeal T : Set A) :=
  sorry

/-- Source wording of `eq_zeroLocus_vanishingIdeal_of_isClosed`: every closed set is the zero
locus of some homogeneous ideal. -/
theorem exists_homogeneousIdeal_zeroLocus_of_isClosed (T : Set (ProjectiveSpectrum 𝒜))
    (hT : IsClosed T) : ∃ I : HomogeneousIdeal 𝒜, T = zeroLocus 𝒜 (I : Set A) :=
  sorry

end ProjectiveSpectrum

end
