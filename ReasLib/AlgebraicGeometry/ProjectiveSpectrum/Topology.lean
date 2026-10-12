/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
public import Mathlib.Topology.Irreducible

@[expose] public section

universe u v

namespace ProjectiveSpectrum

variable {A : Type u} {σ : Type v}
variable [CommRing A] [SetLike σ A] [AddSubmonoidClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The projective spectrum of a graded commutative ring is empty if all sufficiently
high graded pieces are zero. -/
theorem isEmpty_of_eventually_zero
    (h : ∃ N, ∀ n, N ≤ n → ∀ x ∈ 𝒜 n, x = 0) :
    IsEmpty (ProjectiveSpectrum 𝒜) := sorry

/-- The projective spectrum of a graded domain with nonzero irrelevant ideal is an
irreducible topological space. -/
theorem irreducibleSpace_of_isDomain [IsDomain A]
    (h : HomogeneousIdeal.irrelevant 𝒜 ≠ ⊥) :
    IrreducibleSpace (ProjectiveSpectrum 𝒜) := sorry

/-- Eventual vanishing of the graded pieces makes the projective spectrum empty. -/
instance instIsEmptyOfEventuallyZero
    [Fact (∃ N, ∀ n, N ≤ n → ∀ x ∈ 𝒜 n, x = 0)] :
    IsEmpty (ProjectiveSpectrum 𝒜) :=
  isEmpty_of_eventually_zero 𝒜 Fact.out

/-- A graded domain with nonzero irrelevant ideal has irreducible projective spectrum. -/
instance instIrreducibleSpaceOfIsDomain [IsDomain A]
    [Fact (HomogeneousIdeal.irrelevant 𝒜 ≠ ⊥)] :
    IrreducibleSpace (ProjectiveSpectrum 𝒜) :=
  irreducibleSpace_of_isDomain 𝒜 Fact.out

end ProjectiveSpectrum
