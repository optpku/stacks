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
    IsEmpty (ProjectiveSpectrum 𝒜) := by
  obtain ⟨N, hN⟩ := h
  refine ⟨fun x => x.not_irrelevant_le ?_⟩
  rw [HomogeneousIdeal.irrelevant_le]
  intro d hd f hf
  have hNd : N ≤ N • d := by
    rw [nsmul_eq_mul]
    exact Nat.le_mul_of_pos_right N hd
  have hfN : f ^ N = 0 := hN (N • d) hNd (f ^ N) (SetLike.pow_mem_graded N hf)
  apply x.isPrime.mem_of_pow_mem N
  rw [hfN]
  exact x.asHomogeneousIdeal.toIdeal.zero_mem

/-- The projective spectrum of a graded domain with nonzero irrelevant ideal is an
irreducible topological space. -/
theorem irreducibleSpace_of_isDomain [IsDomain A]
    (h : HomogeneousIdeal.irrelevant 𝒜 ≠ ⊥) :
    IrreducibleSpace (ProjectiveSpectrum 𝒜) := by
  let η : ProjectiveSpectrum 𝒜 :=
    { asHomogeneousIdeal := ⊥
      isPrime := by
        change (⊥ : Ideal A).IsPrime
        infer_instance
      not_irrelevant_le := fun hle => h (le_bot_iff.mp hle) }
  have hη : closure ({η} : Set (ProjectiveSpectrum 𝒜)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact (le_iff_mem_closure (𝒜 := 𝒜) η x).mp (show η.asHomogeneousIdeal ≤ x.asHomogeneousIdeal
      from bot_le)
  apply (irreducibleSpace_def (ProjectiveSpectrum 𝒜)).mpr
  change IsIrreducible (Set.univ : Set (ProjectiveSpectrum 𝒜))
  rw [← hη]
  exact isIrreducible_singleton.closure

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
  by
    rw [basicOpen_eq_union_of_projection]
    ext x
    change x ∈ (⨆ i : ℕ, basicOpen 𝒜 (GradedRing.proj 𝒜 i g)) ↔
      x ∈ (basicOpen 𝒜 (GradedRing.proj 𝒜 0 g) ⊔
        ⨆ i : {n : ℕ // 1 ≤ n}, basicOpen 𝒜 (GradedRing.proj 𝒜 i.1 g))
    rw [TopologicalSpace.Opens.mem_iSup, TopologicalSpace.Opens.mem_sup,
      TopologicalSpace.Opens.mem_iSup]
    constructor
    · rintro ⟨i, hi⟩
      rcases Nat.eq_zero_or_pos i with rfl | hi'
      · exact Or.inl hi
      · exact Or.inr ⟨⟨i, hi'⟩, hi⟩
    · rintro (hx | ⟨i, hi⟩)
      · exact ⟨0, hx⟩
      · exact ⟨i.1, hi⟩

/-- A point belongs to the basic open of an element exactly when it belongs to the
basic open of its degree-zero component or of one of its positive-degree components. -/
theorem mem_basicOpen_eq_projZero_sup_iSup_pos (g : A) (x : ProjectiveSpectrum 𝒜) :
    x ∈ basicOpen 𝒜 g ↔
      x ∈ basicOpen 𝒜 (GradedRing.proj 𝒜 0 g) ∨
        ∃ i : {n : ℕ // 1 ≤ n}, x ∈ basicOpen 𝒜 (GradedRing.proj 𝒜 i.1 g) :=
  by
    rw [basicOpen_eq_projZero_sup_iSup_pos 𝒜 g]
    simp only [TopologicalSpace.Opens.mem_sup, TopologicalSpace.Opens.mem_iSup]

/-- The basic open of a degree-zero element is the union of the basic opens of its
products with all positive-degree homogeneous elements. -/
theorem basicOpen_degreeZero_eq_iSup_mul (g₀ : 𝒜 0) :
    basicOpen 𝒜 (g₀ : A) =
      ⨆ d : {n : ℕ // 0 < n}, ⨆ f : 𝒜 d.1,
        basicOpen 𝒜 ((g₀ : A) * (f : A)) :=
  by
    classical
    ext x
    change x ∈ basicOpen 𝒜 (g₀ : A) ↔
      x ∈ (⨆ d : {n : ℕ // 0 < n}, ⨆ f : 𝒜 d.1,
        basicOpen 𝒜 ((g₀ : A) * (f : A)))
    rw [mem_basicOpen, TopologicalSpace.Opens.mem_iSup]
    simp only [TopologicalSpace.Opens.mem_iSup]
    constructor
    · intro hx
      have hex : ∃ d : ℕ, ∃ f : 𝒜 d, 0 < d ∧ (f : A) ∉ x.asHomogeneousIdeal := by
        by_contra! H
        apply x.not_irrelevant_le
        rw [HomogeneousIdeal.irrelevant_le]
        intro d hd f hf
        exact H d ⟨f, hf⟩ hd
      obtain ⟨d, f, hd, hf⟩ := hex
      refine ⟨⟨d, hd⟩, f, ?_⟩
      rw [basicOpen_mul]
      exact ⟨hx, hf⟩
    · rintro ⟨d, f, hxf⟩
      exact basicOpen_mul_le_left 𝒜 _ _ hxf

/-- A point belongs to the basic open of a degree-zero element exactly when it
belongs to the basic open of its product with some positive-degree homogeneous element. -/
theorem mem_basicOpen_degreeZero_iff (g₀ : 𝒜 0) (x : ProjectiveSpectrum 𝒜) :
    x ∈ basicOpen 𝒜 (g₀ : A) ↔
      ∃ d : ℕ, ∃ f : 𝒜 d, 0 < d ∧ x ∈ basicOpen 𝒜 ((g₀ : A) * (f : A)) :=
  by
    rw [basicOpen_degreeZero_eq_iSup_mul 𝒜 g₀]
    simp only [TopologicalSpace.Opens.mem_iSup]
    constructor
    · rintro ⟨⟨d, hd⟩, f, hf⟩
      exact ⟨d, f, hd, hf⟩
    · rintro ⟨d, f, hd, hf⟩
      exact ⟨⟨d, hd⟩, f, hf⟩

/-- The basic opens of positive-degree homogeneous elements form a topological
basis of the projective spectrum. -/
theorem isTopologicalBasis_positiveDegree_basic_opens :
    TopologicalSpace.IsTopologicalBasis
      {U : Set (ProjectiveSpectrum 𝒜) |
        ∃ (n : ℕ) (f : A), 0 < n ∧ f ∈ 𝒜 n ∧
          U = (basicOpen 𝒜 f : Set (ProjectiveSpectrum 𝒜))} :=
  by
    apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
    · rintro _ ⟨n, f, hn, hf, rfl⟩
      exact isOpen_basicOpen 𝒜
    · intro x U hx hU
      obtain ⟨_, ⟨g, rfl⟩, hxg, hgU⟩ :=
        (isTopologicalBasis_basic_opens 𝒜).exists_subset_of_mem_open hx hU
      have hproj (n : ℕ) :
          (basicOpen 𝒜 (GradedRing.proj 𝒜 n g) : Set (ProjectiveSpectrum 𝒜)) ⊆
            basicOpen 𝒜 g := by
        intro y hy
        rw [basicOpen_eq_union_of_projection 𝒜 g]
        exact TopologicalSpace.Opens.mem_iSup.mpr ⟨n, hy⟩
      rcases (mem_basicOpen_eq_projZero_sup_iSup_pos 𝒜 g x).mp hxg with hx₀ | ⟨i, hi⟩
      · let g₀ : 𝒜 0 := DirectSum.decompose 𝒜 g 0
        obtain ⟨d, f, hd, hxf⟩ := (mem_basicOpen_degreeZero_iff 𝒜 g₀ x).mp hx₀
        refine ⟨basicOpen 𝒜 ((g₀ : A) * (f : A)), ⟨d, _, hd, ?_, rfl⟩, hxf, ?_⟩
        · simpa only [zero_add] using SetLike.mul_mem_graded g₀.property f.property
        · have hgU' : (basicOpen 𝒜 g : Set (ProjectiveSpectrum 𝒜)) ⊆ U := hgU
          exact (show (basicOpen 𝒜 ((g₀ : A) * (f : A)) : Set _) ⊆ _ from
            basicOpen_mul_le_left 𝒜 _ _).trans ((hproj 0).trans hgU')
      · refine ⟨basicOpen 𝒜 (GradedRing.proj 𝒜 i.1 g),
          ⟨i.1, _, i.2, ?_, rfl⟩, hi, (hproj i.1).trans hgU⟩
        exact (DirectSum.decompose 𝒜 g i.1).property

/-- Every closed subset of the projective spectrum is the zero locus of a
homogeneous ideal. -/
theorem exists_homogeneousIdeal_zeroLocus_of_isClosed (T : Set (ProjectiveSpectrum 𝒜))
    (hT : IsClosed T) : ∃ I : HomogeneousIdeal 𝒜, T = zeroLocus 𝒜 (I : Set A) := by
  refine ⟨vanishingIdeal T, ?_⟩
  rw [zeroLocus_vanishingIdeal_eq_closure]
  exact hT.closure_eq.symm

end ProjectiveSpectrum
