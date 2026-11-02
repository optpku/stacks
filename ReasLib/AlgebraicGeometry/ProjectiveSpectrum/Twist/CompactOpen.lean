/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.RatioOpenSections

/-!
# Compact opens and projective twisting sheaves

Compact opens of a projective spectrum lie in a ratio open of some positive degree. On every
open contained in such a ratio open, canonical twists and their standard maps retain the
invertibility, isomorphism, and nonvanishing-open properties needed to describe the topology.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open Scheme.Modules
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

section CompactContainment

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- Every compact open of a projective spectrum is contained in the ratio open of some positive
degree. -/
theorem exists_pos_projTwistRatioOpen_containing_of_isCompact
    (Y : (Proj 𝒜).Opens) (hY : IsCompact (Y : Set (Proj 𝒜))) :
    ∃ d : ℕ, 0 < d ∧ Y ≤ projTwistRatioOpen 𝒜 d := by
  classical
  let U (i : Σ n : ℕ+, 𝒜 n) : (Proj 𝒜).Opens := Proj.basicOpen 𝒜 (i.2 : A)
  have hcov : (Y : Set (Proj 𝒜)) ⊆ ⋃ i, (U i : Set (Proj 𝒜)) := by
    intro x _
    let i := (Proj.affineOpenCover 𝒜).idx x
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    change x ∈ Proj.basicOpen 𝒜 (i.2 : A)
    rw [← Proj.opensRange_awayι 𝒜 (i.2 : A) i.2.2 i.1.2]
    exact (Proj.affineOpenCover 𝒜).covers x
  obtain ⟨s, hs⟩ := hY.elim_finite_subcover (fun i => (U i : Set (Proj 𝒜)))
    (fun i => (U i).isOpen) hcov
  let d : ℕ := s.prod (fun i => (i.1 : ℕ))
  have hprod_pos : ∀ t : Finset (Σ n : ℕ+, 𝒜 n),
      0 < t.prod (fun i => (i.1 : ℕ)) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | @insert i t hi ih =>
      rw [Finset.prod_insert hi]
      exact Nat.mul_pos i.1.2 ih
  have hd : 0 < d := hprod_pos s
  refine ⟨d, hd, ?_⟩
  intro x hx
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hs hx)
  have hidvd : (i.1 : ℕ) ∣ d := Finset.dvd_prod_of_mem (fun j => (j.1 : ℕ)) hi
  obtain ⟨k, hk⟩ := hidvd
  have hkpos : 0 < k := by
    apply Nat.pos_of_ne_zero
    rintro rfl
    simpa [hk] using hd
  have hf : (i.2 : A) ^ k ∈ 𝒜 d := by
    rw [hk]
    simpa [nsmul_eq_mul, mul_comm] using SetLike.pow_mem_graded k i.2.2
  have hle : Proj.basicOpen 𝒜 ((i.2 : A) ^ k) ≤ projTwistRatioOpen 𝒜 d := by
    rw [← mul_one ((i.2 : A) ^ k)]
    unfold projTwistRatioOpen
    exact le_iSup_of_le _ (le_iSup_of_le 1 (le_iSup_of_le 0
      (le_iSup_of_le (by simpa using hf)
        (le_iSup_of_le (SetLike.one_mem_graded 𝒜) le_rfl))))
  apply hle
  simpa [U, Proj.basicOpen_pow 𝒜 (i.2 : A) k hkpos] using hxi

private theorem exists_pos_mul_basicOpen_le {d : ℕ} (hd : 0 < d)
    (U : (Proj 𝒜).Opens) (x : Proj 𝒜) (hx : x ∈ U) :
    ∃ n : ℕ+, ∃ f : 𝒜 ((n : ℕ) * d),
      x ∈ Proj.basicOpen 𝒜 (f : A) ∧ Proj.basicOpen 𝒜 (f : A) ≤ U := by
  classical
  obtain ⟨_, ⟨b, rfl⟩, hxb, hbU⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Proj.isBasis_basicOpen 𝒜) hx
  rw [Proj.basicOpen_eq_iSup_proj] at hxb
  obtain ⟨j, hxj⟩ := TopologicalSpace.Opens.mem_iSup.mp hxb
  let i := (Proj.affineOpenCover 𝒜).idx x
  have hxi : x ∈ Proj.basicOpen 𝒜 (i.2 : A) := by
    rw [← Proj.opensRange_awayι 𝒜 (i.2 : A) i.2.2 i.1.2]
    exact (Proj.affineOpenCover 𝒜).covers x
  let n : ℕ+ := ⟨j + (i.1 : ℕ), Nat.add_pos_right j i.1.2⟩
  let g : 𝒜 (n : ℕ) := ⟨GradedRing.proj 𝒜 j b * (i.2 : A),
    SetLike.mul_mem_graded (SetLike.coe_mem ((DirectSum.decompose 𝒜 b) j)) i.2.2⟩
  let f : 𝒜 ((n : ℕ) * d) := ⟨(g : A) ^ d, by
    simpa [nsmul_eq_mul, mul_comm] using SetLike.pow_mem_graded d g.2⟩
  refine ⟨n, f, ?_, ?_⟩
  · change x ∈ Proj.basicOpen 𝒜 ((g : A) ^ d)
    rw [Proj.basicOpen_pow 𝒜 (g : A) d hd]
    change x ∈ Proj.basicOpen 𝒜 (GradedRing.proj 𝒜 j b * (i.2 : A))
    rw [Proj.basicOpen_mul]
    exact ⟨hxj, hxi⟩
  · change Proj.basicOpen 𝒜 ((g : A) ^ d) ≤ U
    rw [Proj.basicOpen_pow 𝒜 (g : A) d hd]
    calc
      Proj.basicOpen 𝒜 (g : A) ≤ Proj.basicOpen 𝒜 (GradedRing.proj 𝒜 j b) := by
        change Proj.basicOpen 𝒜 (GradedRing.proj 𝒜 j b * (i.2 : A)) ≤ _
        rw [Proj.basicOpen_mul]
        exact inf_le_left
      _ ≤ Proj.basicOpen 𝒜 b := by
        rw [Proj.basicOpen_eq_iSup_proj 𝒜 b]
        exact le_iSup (fun i : ℕ => Proj.basicOpen 𝒜 (GradedRing.proj 𝒜 i b)) j
      _ ≤ U := hbU

end CompactContainment

section CanonicalTwists

variable {A : Type u} [CommRing A]
variable (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]

/-- A multiple of a positive ratio degree gives an invertible canonical twist after restriction
to every open contained in the ratio open. -/
theorem projTwist_restrict_open_invertible_of_le_projTwistRatioOpen
    {d : ℕ} (hd : 0 < d) {Y : (Proj 𝒜).Opens}
    (hY : Y ≤ projTwistRatioOpen 𝒜 d) (n : ℤ) :
    Scheme.Modules.Invertible
      ((Scheme.Modules.restrictFunctor Y.ι).obj
        (Proj.AssociatedModule.twistingSheaf 𝒜 (n * (d : ℤ)))) := by
  let W : (Proj 𝒜).Opens := projTwistRatioOpen 𝒜 d
  let j : Y.toScheme ⟶ W.toScheme := Scheme.homOfLE (Proj 𝒜) hY
  let L : (Proj 𝒜).Modules :=
    Proj.AssociatedModule.twistingSheaf 𝒜 (n * (d : ℤ))
  let hW : Scheme.Modules.Invertible ((Scheme.Modules.pullback W.ι).obj L) :=
    projTwist_restrict_ratioOpen_invertible 𝒜 hd n
  letI : Scheme.Modules.Invertible ((Scheme.Modules.pullback W.ι).obj L) := hW
  let hJ : Scheme.Modules.Invertible
      ((Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback W.ι).obj L)) := by
    infer_instance
  let hJW : Scheme.Modules.Invertible
      ((Scheme.Modules.pullback (j ≫ W.ι)).obj L) :=
    CategoryTheory.MonoidalCategory.isInvertibleObject.of_iso
      ((Scheme.Modules.pullbackComp j W.ι).app L) hJ
  have hjι : j ≫ W.ι = Y.ι := by
    exact Scheme.homOfLE_ι (Proj 𝒜) hY
  have hYpull : Scheme.Modules.Invertible
      ((Scheme.Modules.pullback Y.ι).obj L) := by
    simpa [hjι] using hJW
  exact CategoryTheory.MonoidalCategory.isInvertibleObject.of_iso
    ((Scheme.Modules.restrictFunctorIsoPullback Y.ι).app L).symm hYpull

/-- Canonical twist multiplication with first index a multiple of a positive ratio degree is an
isomorphism after restriction to every open contained in the ratio open. -/
theorem projTwistMul_restrict_open_isIso_of_le_projTwistRatioOpen
    (T : Proj.AssociatedModule.TwistMultiplication 𝒜)
    {d : ℕ} (hd : 0 < d) {Y : (Proj 𝒜).Opens}
    (hY : Y ≤ projTwistRatioOpen 𝒜 d) (n m : ℤ) :
    IsIso
      (Proj.AssociatedModule.TwistMultiplication.restrictOpenMap
        𝒜 T Y (n * (d : ℤ)) m) := sorry

namespace Proj.AssociatedModule

/-- On an open contained in a positive-degree ratio open, the nonvanishing open of the canonical
section determined by a homogeneous element is the inverse image of its projective basic open. -/
theorem sectionNonvanishingOpen_twistSectionOnOpen_of_le_ratioOpen
    {d n : ℕ} (hd : 0 < d) (hn : 0 < n) {Y : (Proj 𝒜).Opens}
    (hY : Y ≤ projTwistRatioOpen 𝒜 d) (f : 𝒜 (n * d)) :
    (Eq.mp
      (congrArg
        (fun k : ℤ => Scheme.Modules.Invertible
          ((Scheme.Modules.restrictFunctor Y.ι).obj
            (Proj.AssociatedModule.twistingSheaf 𝒜 k)))
        (Int.natCast_mul n d).symm)
      (projTwist_restrict_open_invertible_of_le_projTwistRatioOpen
        𝒜 hd hY (n : ℤ))).sectionNonvanishingOpen
        (Proj.AssociatedModule.twistSectionOnOpen 𝒜 Y f) =
      Y.ι ⁻¹ᵁ Proj.basicOpen 𝒜 (f : A) := by
  exact sectionNonvanishingOpen_twistSectionOnOpen 𝒜 Y (Nat.mul_pos hn hd) f _

private theorem exists_twistSectionOnOpen_nonvanishingOpen_eq_preimage {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (Y : (Proj 𝒜).Opens) (f : 𝒜 (n * d))
    (hL : Scheme.Modules.Invertible ((Scheme.Modules.restrictFunctor Y.ι).obj
      (Proj.AssociatedModule.twistingSheaf 𝒜 ((n : ℤ) * (d : ℤ))))) :
    ∃ s : Γ((Scheme.Modules.restrictFunctor Y.ι).obj
        (Proj.AssociatedModule.twistingSheaf 𝒜 ((n : ℤ) * (d : ℤ))), ⊤),
      hL.sectionNonvanishingOpen s = Y.ι ⁻¹ᵁ Proj.basicOpen 𝒜 (f : A) := by
  revert hL
  rw [← Int.natCast_mul]
  intro hL
  exact ⟨Proj.AssociatedModule.twistSectionOnOpen 𝒜 Y f,
    Proj.AssociatedModule.sectionNonvanishingOpen_twistSectionOnOpen
      𝒜 Y (Nat.mul_pos hn hd) f hL⟩


end Proj.AssociatedModule

/-- The nonvanishing opens of all global sections of the positive multiples of a canonical twist
degree form a basis on every open contained in the corresponding ratio open. -/
theorem isBasis_projTwistSectionNonvanishingOpen_of_le_projTwistRatioOpen
    {d : ℕ} (hd : 0 < d) {Y : (Proj 𝒜).Opens}
    (hY : Y ≤ projTwistRatioOpen 𝒜 d) :
    TopologicalSpace.Opens.IsBasis
      {U : Y.toScheme.Opens |
        ∃ n : ℕ+,
          ∃ s : Γ((Scheme.Modules.restrictFunctor Y.ι).obj
              (Proj.AssociatedModule.twistingSheaf 𝒜 ((n : ℤ) * (d : ℤ))), ⊤),
            U = (projTwist_restrict_open_invertible_of_le_projTwistRatioOpen
              𝒜 hd hY (n : ℤ)).sectionNonvanishingOpen s} := by
  rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
  intro U x hx
  obtain ⟨n, f, hxf, hfU⟩ := exists_pos_mul_basicOpen_le 𝒜 hd (Y.ι ''ᵁ U)
    (Y.ι x) (by exact ⟨x, hx, rfl⟩)
  obtain ⟨s, hs⟩ := Proj.AssociatedModule.exists_twistSectionOnOpen_nonvanishingOpen_eq_preimage 𝒜 hd n.2 Y f
    (projTwist_restrict_open_invertible_of_le_projTwistRatioOpen 𝒜 hd hY (n : ℤ))
  refine ⟨Y.ι ⁻¹ᵁ Proj.basicOpen 𝒜 (f : A), ⟨n, s, hs.symm⟩, hxf, ?_⟩
  intro y hy
  exact (Y.ι.apply_mem_image_iff).mp (hfU hy)

/-- The affine nonvanishing opens among all global sections of the positive multiples of a
canonical twist degree form a basis on every open contained in the corresponding ratio open. -/
theorem isBasis_affine_projTwistSectionNonvanishingOpen_of_le_projTwistRatioOpen
    {d : ℕ} (hd : 0 < d) {Y : (Proj 𝒜).Opens}
    (hY : Y ≤ projTwistRatioOpen 𝒜 d) :
    TopologicalSpace.Opens.IsBasis
      {U : Y.toScheme.Opens |
        ∃ n : ℕ+,
          ∃ s : Γ((Scheme.Modules.restrictFunctor Y.ι).obj
              (Proj.AssociatedModule.twistingSheaf 𝒜 ((n : ℤ) * (d : ℤ))), ⊤),
            U = (projTwist_restrict_open_invertible_of_le_projTwistRatioOpen
                𝒜 hd hY (n : ℤ)).sectionNonvanishingOpen s ∧
              IsAffineOpen U} := by
  rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
  intro U x hx
  obtain ⟨n, f, hxf, hfU⟩ := exists_pos_mul_basicOpen_le 𝒜 hd (Y.ι ''ᵁ U)
    (Y.ι x) (by exact ⟨x, hx, rfl⟩)
  obtain ⟨s, hs⟩ := Proj.AssociatedModule.exists_twistSectionOnOpen_nonvanishingOpen_eq_preimage 𝒜 hd n.2 Y f
    (projTwist_restrict_open_invertible_of_le_projTwistRatioOpen 𝒜 hd hY (n : ℤ))
  refine ⟨Y.ι ⁻¹ᵁ Proj.basicOpen 𝒜 (f : A), ⟨n, s, hs.symm, ?_⟩, hxf, ?_⟩
  · exact (Proj.isAffineOpen_basicOpen 𝒜 (f : A) f.2 (Nat.mul_pos n.2 hd)).preimage_of_isOpenImmersion
      Y.ι (by simpa using hfU.trans (Y.ι_image_le U))
  · intro y hy
    exact (Y.ι.apply_mem_image_iff).mp (hfU hy)

end CanonicalTwists

namespace Proj.AssociatedModule.ShiftComparison

variable {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
variable (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
variable (ℳ : ℤ → Submodule ℤ M) [SetLike.GradedSMul 𝒜 ℳ]

/-- A standard shift comparison at an index divisible by a positive ratio degree is an
isomorphism after restriction to every open contained in the ratio open. -/
theorem restrictOpen_isIso_of_le_projTwistRatioOpen
    (C : Proj.AssociatedModule.ShiftComparison 𝒜 ℳ)
    {d : ℕ} (hd : 0 < d) {Y : (Proj 𝒜).Opens}
    (hY : Y ≤ projTwistRatioOpen 𝒜 d) (n : ℤ) :
    IsIso (restrictOpenMap 𝒜 ℳ C Y (n * (d : ℤ))) := by
  let W : (Proj 𝒜).Opens := projTwistRatioOpen 𝒜 d
  let j : Y.toScheme ⟶ W.toScheme := (Proj 𝒜).homOfLE hY
  let φ := C.hom (n * (d : ℤ))
  haveI : IsIso (restrictOpenMap 𝒜 ℳ C W (n * (d : ℤ))) :=
    restrictRatioOpen_isIso 𝒜 ℳ C hd n
  haveI : IsIso ((Scheme.Modules.pullbackTensorIso W.ι _ _).inv ≫
      (Scheme.Modules.pullback W.ι).map φ) := by
    change IsIso (restrictOpenMap 𝒜 ℳ C W (n * (d : ℤ)))
    infer_instance
  haveI : IsIso ((Scheme.Modules.pullback W.ι).map φ) := by
    apply IsIso.of_isIso_comp_left (Scheme.Modules.pullbackTensorIso W.ι _ _).inv
  have hs : IsIso ((Scheme.Modules.pullback W.ι ⋙ Scheme.Modules.pullback j).map φ) := by
    change IsIso ((Scheme.Modules.pullback j).map
      ((Scheme.Modules.pullback W.ι).map φ))
    infer_instance
  have hc : IsIso ((Scheme.Modules.pullback (j ≫ W.ι)).map φ) :=
    (NatIso.isIso_map_iff (Scheme.Modules.pullbackComp j W.ι) φ).mp hs
  have hjι : j ≫ W.ι = Y.ι := Scheme.homOfLE_ι (Proj 𝒜) hY
  haveI : IsIso ((Scheme.Modules.pullback Y.ι).map φ) :=
    (NatIso.isIso_map_iff (Scheme.Modules.pullbackCongr hjι) φ).mp hc
  change IsIso ((Scheme.Modules.pullbackTensorIso Y.ι _ _).inv ≫
    (Scheme.Modules.pullback Y.ι).map φ)
  infer_instance

end Proj.AssociatedModule.ShiftComparison

end AlgebraicGeometry
