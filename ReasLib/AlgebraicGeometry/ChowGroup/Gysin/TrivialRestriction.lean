/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin

/-!
# Cycle-level Gysin maps for trivial restrictions

This file defines the cycle-valued Gysin map associated to a section of an invertible
module whose pullback to its zero scheme is trivial, together with its generator formulas
and compatibility with Chow classes.
-/

@[expose] public section

open CategoryTheory Function Set Topology

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S]
  [LocallyOfFiniteType p] (δ : S → ℤ) [IsDimensionFunction δ]
  (ℒ : X.Modules) [Invertible ℒ] (s : ℒ.sections)

/-- The cycle contributed by a degree-`k + 1` point when the restriction of `ℒ` to
`Z(s)` is trivial: it is zero on `Z(s)` and the scheme-theoretic intersection cycle
away from `Z(s)`. -/
noncomputable def trivialGysinGeneratorCycle
    (htriv : RingedSpace.IsTrivial ((pullback (zeroSchemeι ℒ s)).obj ℒ))
    (k : ℤ) (x : X) (hx : p.relativeDimensionFunction δ x = k + 1) :
    CycleGroup (zeroScheme ℒ s)
      ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k :=
  @dite _ (x ∈ (zeroIdealSheaf ℒ s).support) (Classical.propDecidable _)
    (fun _ ↦ 0)
    (fun _ ↦
      CycleGroup.mapHom (zeroPointIntersectionToZeroScheme ℒ s x)
        (((zeroPointIntersection ℒ s x).subschemeι ≫ p).relativeDimensionFunction δ)
        ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k
        (zeroPointIntersectionFundamentalCycle p δ ℒ s k x))

/-- A generator supported on `Z(s)` contributes zero to the trivial-restriction Gysin
cycle. -/
theorem trivialGysinGeneratorCycle_of_mem
    (htriv : RingedSpace.IsTrivial ((pullback (zeroSchemeι ℒ s)).obj ℒ))
    (k : ℤ) (x : X) (hx : p.relativeDimensionFunction δ x = k + 1)
    (hmem : x ∈ (zeroIdealSheaf ℒ s).support) :
    trivialGysinGeneratorCycle p δ ℒ s htriv k x hx = 0 := by
  simp [trivialGysinGeneratorCycle, hmem]

/-- A generator away from `Z(s)` contributes the pushed-forward fundamental cycle of
its scheme-theoretic intersection with `Z(s)`. -/
theorem trivialGysinGeneratorCycle_of_not_mem
    (htriv : RingedSpace.IsTrivial ((pullback (zeroSchemeι ℒ s)).obj ℒ))
    (k : ℤ) (x : X) (hx : p.relativeDimensionFunction δ x = k + 1)
    (hmem : x ∉ (zeroIdealSheaf ℒ s).support) :
    trivialGysinGeneratorCycle p δ ℒ s htriv k x hx =
      CycleGroup.mapHom (zeroPointIntersectionToZeroScheme ℒ s x)
        (((zeroPointIntersection ℒ s x).subschemeι ≫ p).relativeDimensionFunction δ)
        ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k
        (zeroPointIntersectionFundamentalCycle p δ ℒ s k x) := by
  simp [trivialGysinGeneratorCycle, hmem]

private theorem trivialGysinGeneratorCycle_support
    (htriv : RingedSpace.IsTrivial ((pullback (zeroSchemeι ℒ s)).obj ℒ))
    (k : ℤ) (x : X) (hx : p.relativeDimensionFunction δ x = k + 1) :
    (CycleGroup.toAlgebraicCycle
      ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k
      (trivialGysinGeneratorCycle p δ ℒ s htriv k x hx)).support ⊆
        (zeroSchemeι ℒ s) ⁻¹' closure ({x} : Set X) := by
  by_cases hmem : x ∈ (zeroIdealSheaf ℒ s).support
  · simp [trivialGysinGeneratorCycle_of_mem p δ ℒ s htriv k x hx hmem]
  · rw [trivialGysinGeneratorCycle_of_not_mem p δ ℒ s htriv k x hx hmem]
    change (AlgebraicCycle.map (zeroPointIntersectionToZeroScheme ℒ s x)
      (((zeroPointIntersection ℒ s x).subschemeι ≫ p).relativeDimensionFunction δ)
      ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ)
      (CycleGroup.toAlgebraicCycle
        (((zeroPointIntersection ℒ s x).subschemeι ≫ p).relativeDimensionFunction δ) k
        (zeroPointIntersectionFundamentalCycle p δ ℒ s k x))).support ⊆ _
    refine Function.locallyFinsupp.support_map_subset_of_forall_mem
      (hf := (zeroPointIntersectionToZeroScheme ℒ s x).isSpectralMap)
      (w := _) (c := _) Set.univ _ (Set.subset_univ _) ?_
    intro y _ _
    have hy : (zeroPointIntersection ℒ s x).subschemeι y ∈
        (Scheme.PointClosure.reducedStructure x).ideal.support :=
      Scheme.IdealSheafData.support_antitone
        (le_sup_right : (Scheme.PointClosure.reducedStructure x).ideal ≤
          zeroPointIntersection ℒ s x) y.property
    rw [(Scheme.PointClosure.reducedStructure x).support_eq] at hy
    change (zeroSchemeι ℒ s) (zeroPointIntersectionToZeroScheme ℒ s x y) ∈
      closure ({x} : Set X)
    have hcomp : zeroPointIntersectionToZeroScheme ℒ s x ≫ zeroSchemeι ℒ s =
        (zeroPointIntersection ℒ s x).subschemeι :=
      Scheme.IdealSheafData.inclusion_subschemeι
        (le_sup_left : zeroIdealSheaf ℒ s ≤ zeroPointIntersection ℒ s x)
    rw [← Scheme.Hom.comp_apply]
    rw [hcomp]
    exact hy

/-- The coefficient-weighted trivial-restriction Gysin generator cycles form a locally
finite family on `Z(s)`. -/
theorem trivialGysinGeneratorTermsLocallyFinite
    (htriv : RingedSpace.IsTrivial ((pullback (zeroSchemeι ℒ s)).obj ℒ))
    (k : ℤ) (α : CycleGroup X (p.relativeDimensionFunction δ) (k + 1)) :
    LocallyFinite fun x : X ↦
      (CycleGroup.toAlgebraicCycle
        ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k
        (if hx : p.relativeDimensionFunction δ x = k + 1 then
          (CycleGroup.toAlgebraicCycle (p.relativeDimensionFunction δ) (k + 1) α x) •
            trivialGysinGeneratorCycle p δ ℒ s htriv k x hx
        else 0)).support := by
  intro z
  obtain ⟨U, hU, hfin⟩ :=
    (CycleGroup.toAlgebraicCycle (p.relativeDimensionFunction δ) (k + 1) α).locallyFiniteSupport
      (zeroSchemeι ℒ s z)
  obtain ⟨V, hVU, hV, hzV⟩ := mem_nhds_iff.mp hU
  refine ⟨(zeroSchemeι ℒ s) ⁻¹' V,
    (hV.preimage (zeroSchemeι ℒ s).continuous).mem_nhds hzV, hfin.subset ?_⟩
  intro x hx
  obtain ⟨y, hy, hyV⟩ := hx
  by_cases hdim : p.relativeDimensionFunction δ x = k + 1
  · have hcoeff : CycleGroup.toAlgebraicCycle
        (p.relativeDimensionFunction δ) (k + 1) α x ≠ 0 := by
      intro hzero
      simpa [hdim, hzero] using hy
    have hgen : y ∈ (CycleGroup.toAlgebraicCycle
        ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k
        (trivialGysinGeneratorCycle p δ ℒ s htriv k x hdim)).support := by
      intro hzero
      apply hy
      simp [hdim, map_zsmul, Function.locallyFinsuppWithin.coe_zsmul, hzero]
    have hclosure := trivialGysinGeneratorCycle_support p δ ℒ s htriv k x hdim hgen
    obtain ⟨w, hwV, hwx⟩ := mem_closure_iff.mp hclosure V hV hyV
    have hxV : x ∈ V := by simpa only [Set.mem_singleton_iff.mp hwx] using hwV
    exact ⟨hVU hxV, hcoeff⟩
  · simpa [hdim] using hy

/-- The explicit cycle obtained by extending the trivial-restriction generator rule
linearly. -/
noncomputable def trivialGysinCycle
    (htriv : RingedSpace.IsTrivial ((pullback (zeroSchemeι ℒ s)).obj ℒ))
    (k : ℤ) (α : CycleGroup X (p.relativeDimensionFunction δ) (k + 1)) :
    CycleGroup (zeroScheme ℒ s)
      ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k :=
  CycleGroup.locallyFiniteSum
    ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k
    (fun x : X ↦
      if hx : p.relativeDimensionFunction δ x = k + 1 then
        (CycleGroup.toAlgebraicCycle (p.relativeDimensionFunction δ) (k + 1) α x) •
          trivialGysinGeneratorCycle p δ ℒ s htriv k x hx
      else 0)
    (trivialGysinGeneratorTermsLocallyFinite p δ ℒ s htriv k α)

/-- Coefficients of the trivial-restriction Gysin cycle are the pointwise finite sums of
the weighted generator cycles. -/
theorem trivialGysinCycle_apply
    (htriv : RingedSpace.IsTrivial ((pullback (zeroSchemeι ℒ s)).obj ℒ))
    (k : ℤ) (α : CycleGroup X (p.relativeDimensionFunction δ) (k + 1))
    (z : zeroScheme ℒ s) :
    CycleGroup.toAlgebraicCycle
        ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k
        (trivialGysinCycle p δ ℒ s htriv k α) z =
      ∑ᶠ x : X,
        CycleGroup.toAlgebraicCycle
          ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k
          (if hx : p.relativeDimensionFunction δ x = k + 1 then
            (CycleGroup.toAlgebraicCycle (p.relativeDimensionFunction δ) (k + 1) α x) •
              trivialGysinGeneratorCycle p δ ℒ s htriv k x hx
          else 0) z := by
  rfl

/-- The concrete trivial-restriction Gysin cycle sends zero to zero. -/
theorem trivialGysinCycle_zero
    (htriv : RingedSpace.IsTrivial ((pullback (zeroSchemeι ℒ s)).obj ℒ)) (k : ℤ) :
    trivialGysinCycle p δ ℒ s htriv k 0 = 0 := by
  apply Subtype.ext
  apply DFunLike.ext
  intro z
  change CycleGroup.toAlgebraicCycle
      ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k
      (trivialGysinCycle p δ ℒ s htriv k 0) z = 0
  rw [trivialGysinCycle_apply]
  simp

/-- The concrete trivial-restriction Gysin cycle preserves addition. -/
theorem trivialGysinCycle_add
    (htriv : RingedSpace.IsTrivial ((pullback (zeroSchemeι ℒ s)).obj ℒ))
    (k : ℤ) (α β : CycleGroup X (p.relativeDimensionFunction δ) (k + 1)) :
    trivialGysinCycle p δ ℒ s htriv k (α + β) =
      trivialGysinCycle p δ ℒ s htriv k α + trivialGysinCycle p δ ℒ s htriv k β := by
  let c (γ : CycleGroup X (p.relativeDimensionFunction δ) (k + 1)) (x : X) :=
    if hx : p.relativeDimensionFunction δ x = k + 1 then
      (CycleGroup.toAlgebraicCycle (p.relativeDimensionFunction δ) (k + 1) γ x) •
        trivialGysinGeneratorCycle p δ ℒ s htriv k x hx
    else 0
  have hc (γ : CycleGroup X (p.relativeDimensionFunction δ) (k + 1)) :
      LocallyFinite fun x ↦ (CycleGroup.toAlgebraicCycle
        ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k (c γ x)).support :=
    trivialGysinGeneratorTermsLocallyFinite p δ ℒ s htriv k γ
  have hadd (x : X) : c (α + β) x = c α x + c β x := by
    dsimp only [c]
    split_ifs with hx
    · show (CycleGroup.toAlgebraicCycle (p.relativeDimensionFunction δ) (k + 1)
          (α + β) x) • trivialGysinGeneratorCycle p δ ℒ s htriv k x hx =
        (CycleGroup.toAlgebraicCycle (p.relativeDimensionFunction δ) (k + 1) α x) •
            trivialGysinGeneratorCycle p δ ℒ s htriv k x hx +
          (CycleGroup.toAlgebraicCycle (p.relativeDimensionFunction δ) (k + 1) β x) •
            trivialGysinGeneratorCycle p δ ℒ s htriv k x hx
      simp [add_zsmul]
    · simp
  apply Subtype.ext
  apply DFunLike.ext
  intro z
  change (∑ᶠ x, CycleGroup.toAlgebraicCycle
      ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k (c (α + β) x) z) =
    (∑ᶠ x, CycleGroup.toAlgebraicCycle
      ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k (c α x) z) +
    ∑ᶠ x, CycleGroup.toAlgebraicCycle
      ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k (c β x) z
  simp_rw [hadd, map_add, Function.locallyFinsuppWithin.coe_add, Pi.add_apply]
  exact finsum_add_distrib ((hc α).point_finite z) ((hc β).point_finite z)

/-- The canonical additive cycle map associated to a section whose line bundle becomes
trivial on its zero scheme. -/
noncomputable def trivialGysin
    (htriv : RingedSpace.IsTrivial ((pullback (zeroSchemeι ℒ s)).obj ℒ)) (k : ℤ) :
    CycleGroup X (p.relativeDimensionFunction δ) (k + 1) →+
      CycleGroup (zeroScheme ℒ s)
        ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k where
  toFun := trivialGysinCycle p δ ℒ s htriv k
  map_zero' := trivialGysinCycle_zero p δ ℒ s htriv k
  map_add' := trivialGysinCycle_add p δ ℒ s htriv k

private theorem trivialGysinCycle_point
    (htriv : RingedSpace.IsTrivial ((pullback (zeroSchemeι ℒ s)).obj ℒ))
    (k : ℤ) (x : X) (hx : p.relativeDimensionFunction δ x = k + 1) :
    trivialGysinCycle p δ ℒ s htriv k
        (CycleGroup.point (p.relativeDimensionFunction δ) (k + 1) x hx) =
      trivialGysinGeneratorCycle p δ ℒ s htriv k x hx := by
  classical
  apply Subtype.ext
  apply DFunLike.ext
  intro z
  change CycleGroup.toAlgebraicCycle
      ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k
      (trivialGysinCycle p δ ℒ s htriv k
        (CycleGroup.point (p.relativeDimensionFunction δ) (k + 1) x hx)) z = _
  rw [trivialGysinCycle_apply, finsum_eq_single _ x]
  · simp [hx, CycleGroup.toAlgebraicCycle, CycleGroup.point]
  · intro y hy
    by_cases hy' : p.relativeDimensionFunction δ y = k + 1
    · simp [hy', CycleGroup.toAlgebraicCycle, CycleGroup.point, hy]
    · simp [hy']

/-- On a point generator contained in `Z(s)`, the trivial-restriction Gysin map is zero. -/
theorem trivialGysin_point_of_mem
    (htriv : RingedSpace.IsTrivial ((pullback (zeroSchemeι ℒ s)).obj ℒ))
    (k : ℤ) (x : X) (hx : p.relativeDimensionFunction δ x = k + 1)
    (hmem : x ∈ (zeroIdealSheaf ℒ s).support) :
    trivialGysin p δ ℒ s htriv k
        (CycleGroup.point (p.relativeDimensionFunction δ) (k + 1) x hx) = 0 := by
  change trivialGysinCycle p δ ℒ s htriv k
    (CycleGroup.point (p.relativeDimensionFunction δ) (k + 1) x hx) = 0
  rw [trivialGysinCycle_point, trivialGysinGeneratorCycle_of_mem p δ ℒ s htriv k x hx hmem]

/-- On a point generator away from `Z(s)`, the trivial-restriction Gysin map is the
pushed-forward scheme-theoretic intersection cycle. -/
theorem trivialGysin_point_of_not_mem
    (htriv : RingedSpace.IsTrivial ((pullback (zeroSchemeι ℒ s)).obj ℒ))
    (k : ℤ) (x : X) (hx : p.relativeDimensionFunction δ x = k + 1)
    (hmem : x ∉ (zeroIdealSheaf ℒ s).support) :
    trivialGysin p δ ℒ s htriv k
        (CycleGroup.point (p.relativeDimensionFunction δ) (k + 1) x hx) =
      CycleGroup.mapHom (zeroPointIntersectionToZeroScheme ℒ s x)
        (((zeroPointIntersection ℒ s x).subschemeι ≫ p).relativeDimensionFunction δ)
        ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) k
        (zeroPointIntersectionFundamentalCycle p δ ℒ s k x) := by
  change trivialGysinCycle p δ ℒ s htriv k
    (CycleGroup.point (p.relativeDimensionFunction δ) (k + 1) x hx) = _
  rw [trivialGysinCycle_point,
    trivialGysinGeneratorCycle_of_not_mem p δ ℒ s htriv k x hx hmem]

/-- Passage to Chow classes identifies the trivial-restriction cycle map with the Gysin
homomorphism. -/
theorem trivialGysin_chowClass
    (htriv : RingedSpace.IsTrivial ((pullback (zeroSchemeι ℒ s)).obj ℒ))
    (k : ℤ) (α : CycleGroup X (p.relativeDimensionFunction δ) (k + 1)) :
    @chowClass (zeroScheme ℒ s)
        (@zeroSchemeIsLocallyNoetherian X (LocallyOfFiniteType.isLocallyNoetherian p)
          ℒ inferInstance s)
        ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) inferInstance k
        (trivialGysin p δ ℒ s htriv k α) =
      gysin p δ ℒ s k α := sorry

end AlgebraicGeometry.Scheme.Modules
