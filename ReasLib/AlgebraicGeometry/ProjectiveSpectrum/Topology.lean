/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
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

/-- The basic open of an element is the union of the basic open of its degree-zero
component and the basic opens of its positive-degree components. -/
theorem basicOpen_eq_projZero_sup_iSup_pos (g : A) :
    basicOpen 𝒜 g =
      basicOpen 𝒜 (GradedRing.proj 𝒜 0 g) ⊔
        ⨆ i : {n : ℕ // 1 ≤ n}, basicOpen 𝒜 (GradedRing.proj 𝒜 i.1 g) :=
  sorry

/-- A point belongs to the basic open of an element exactly when it belongs to the
basic open of its degree-zero component or of one of its positive-degree components. -/
theorem mem_basicOpen_eq_projZero_sup_iSup_pos (g : A) (x : ProjectiveSpectrum 𝒜) :
    x ∈ basicOpen 𝒜 g ↔
      x ∈ basicOpen 𝒜 (GradedRing.proj 𝒜 0 g) ∨
        ∃ i : {n : ℕ // 1 ≤ n}, x ∈ basicOpen 𝒜 (GradedRing.proj 𝒜 i.1 g) :=
  sorry

/-- The basic open of a degree-zero element is the union of the basic opens of its
products with all positive-degree homogeneous elements. -/
theorem basicOpen_degreeZero_eq_iSup_mul (g₀ : 𝒜 0) :
    basicOpen 𝒜 (g₀ : A) =
      ⨆ d : {n : ℕ // 0 < n}, ⨆ f : 𝒜 d.1,
        basicOpen 𝒜 ((g₀ : A) * (f : A)) :=
  sorry

/-- A point belongs to the basic open of a degree-zero element exactly when it
belongs to the basic open of its product with some positive-degree homogeneous element. -/
theorem mem_basicOpen_degreeZero_iff (g₀ : 𝒜 0) (x : ProjectiveSpectrum 𝒜) :
    x ∈ basicOpen 𝒜 (g₀ : A) ↔
      ∃ d : ℕ, ∃ f : 𝒜 d, 0 < d ∧ x ∈ basicOpen 𝒜 ((g₀ : A) * (f : A)) :=
  sorry

/-- The basic opens of positive-degree homogeneous elements form a topological
basis of the projective spectrum. -/
theorem isTopologicalBasis_positiveDegree_basic_opens :
    TopologicalSpace.IsTopologicalBasis
      {U : Set (ProjectiveSpectrum 𝒜) |
        ∃ (n : ℕ) (f : A), 0 < n ∧ f ∈ 𝒜 n ∧
          U = (basicOpen 𝒜 f : Set (ProjectiveSpectrum 𝒜))} :=
  sorry

/-- Every closed subset of the projective spectrum is the zero locus of a
homogeneous ideal. -/
theorem exists_homogeneousIdeal_zeroLocus_of_isClosed (T : Set (ProjectiveSpectrum 𝒜))
    (hT : IsClosed T) : ∃ I : HomogeneousIdeal 𝒜, T = zeroLocus 𝒜 (I : Set A) := by
  refine ⟨vanishingIdeal T, ?_⟩
  rw [zeroLocus_vanishingIdeal_eq_closure]
  sorry

end ProjectiveSpectrum
