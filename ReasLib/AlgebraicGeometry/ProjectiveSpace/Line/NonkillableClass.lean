/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Line.Curve
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TopSections
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.IdealSheaf
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Union
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.Boundary
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections

/-!
# A non-killable H¹ class on the projective line

The ideal sheaf of `{0, ∞} ⊂ ℙ¹_k` is invertible, and the connecting class of the
indicator section of `i_* 𝒪_Z` at `0` remains nonzero after pullback along every
finite surjective scheme morphism.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData
open CategoryTheory CategoryTheory.Limits
open Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveLine.NonkillableClass

variable (k : Type u) [Field k]

/-- The homogeneous zero locus `V(y)` on `ℙ¹_k`, whose unique closed point is `0 = [1 : 0]`. -/
def zeroLocus : Closeds (scheme k) :=
  ⟨ProjectiveSpectrum.zeroLocus (grading k) {y k},
    ProjectiveSpectrum.isClosed_zeroLocus _ _⟩

/-- The homogeneous zero locus `V(x)` on `ℙ¹_k`, whose unique closed point is `∞ = [0 : 1]`. -/
def infinityLocus : Closeds (scheme k) :=
  ⟨ProjectiveSpectrum.zeroLocus (grading k) {x k},
    ProjectiveSpectrum.isClosed_zeroLocus _ _⟩

/-- The reduced closed subscheme `Z = {0, ∞}` of `ℙ¹_k`, as the scheme-theoretic union of `V(y)`
and `V(x)`. In the ideal-sheaf lattice this is the infimum, equivalently
`vanishingIdeal (zeroLocus k ⊔ infinityLocus k)`. -/
def twoPointDivisor : (scheme k).IdealSheafData :=
  vanishingIdeal (zeroLocus k) ⊓ vanishingIdeal (infinityLocus k)

/-- `twoPointDivisor k` is the vanishing ideal of the closed set `{0, ∞}`. -/
theorem twoPointDivisor_eq :
    twoPointDivisor k = vanishingIdeal (zeroLocus k ⊔ infinityLocus k) := by
  simp [twoPointDivisor]

/-- The affine zero section is evaluation at zero in polynomial coordinates. -/
private theorem affineLineZero_comp_specIso :
    affineLineZero k ≫ (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (.of k)).hom =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.eval₂Hom (RingHom.id k) (fun _ : ULift.{u} (Fin 1) ↦ 0))) := by
  apply (cancel_mono (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (.of k)).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply AffineSpace.hom_ext
  · simp only [affineLineZero, AffineSpace.homOfVector_over,
      Category.assoc, AffineSpace.SpecIso_inv_over, ← Spec.map_comp]
    symm
    rw [Spec.map_eq_id]
    ext r : 2
    simp
  · intro j
    rw [affineLineZero, AffineSpace.homOfVector_appTop_coord,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      AffineSpace.SpecIso_inv_appTop_coord, ← CommRingCat.comp_apply,
      ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
    change 0 = (Scheme.ΓSpecIso (CommRingCat.of k)).inv
      ((MvPolynomial.eval₂Hom (RingHom.id k) (fun _ : ULift.{u} (Fin 1) ↦ 0)) (MvPolynomial.X j))
    simp only [MvPolynomial.eval₂Hom_X', map_zero]

/-- The other homogeneous coordinate vanishes at the zero of either standard chart. -/
private theorem zeroOnChart_coordinate_mem (i : Fin 2) :
    coordinate k (i.succAbove 0) ∈
      (((affineLineZero k ≫ (ProjectiveSpace.CoordinateChart.iso (R := k) 1 i).inv) ≫
          (ProjectiveSpace.coordinateBasicOpen (R := k) 1 i).1.ι).base
        (IsLocalRing.closedPoint k)).asHomogeneousIdeal := by
  let q : (ProjectiveSpace.coordinateBasicOpen (R := k) 1 i).1.toScheme :=
    (affineLineZero k ≫ (ProjectiveSpace.CoordinateChart.iso (R := k) 1 i).inv).base
      (IsLocalRing.closedPoint k)
  let t : HomogeneousLocalization.NumDenSameDeg (grading k)
      (Submonoid.powers (coordinate k i)) :=
    ⟨1, ⟨coordinate k (i.succAbove 0), MvPolynomial.isHomogeneous_X k (i.succAbove 0)⟩,
      ⟨coordinate k i, MvPolynomial.isHomogeneous_X k i⟩, ⟨1, by simp⟩⟩
  have hmap : affineLineZero k ≫ (ProjectiveSpace.CoordinateChart.iso (R := k) 1 i).inv ≫
      (Proj.basicOpenIsoSpec (grading k) (coordinate k i)
        (MvPolynomial.isHomogeneous_X k i) Nat.zero_lt_one).hom =
      Spec.map (CommRingCat.ofHom ((MvPolynomial.eval₂Hom (RingHom.id k)
        (fun _ : ULift.{u} (Fin 1) ↦ 0)).comp
        (ProjectiveSpace.CoordinateChart.dehomogenization (R := k) 1 i Equiv.ulift.symm))) := by
    simp only [ProjectiveSpace.CoordinateChart.iso,
      ProjectiveSpace.CoordinateChart.isoWith, Iso.trans_inv, Iso.symm_inv,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
    erw [← Category.assoc, affineLineZero_comp_specIso k]
    simp only [Functor.mapIso_hom, Iso.op_hom, Scheme.Spec_map, Quiver.Hom.unop_op]
    erw [← Spec.map_comp]
    rfl
  apply (ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply (grading k) q t).mp
  change HomogeneousLocalization.mk t ∈
    ((affineLineZero k ≫ (ProjectiveSpace.CoordinateChart.iso (R := k) 1 i).inv ≫
      (Proj.basicOpenIsoSpec (grading k) (coordinate k i)
        (MvPolynomial.isHomogeneous_X k i) Nat.zero_lt_one).hom).base
      (IsLocalRing.closedPoint k)).asIdeal
  rw [hmap]
  change ((MvPolynomial.eval₂Hom (RingHom.id k) (fun _ : ULift.{u} (Fin 1) ↦ 0))
    (ProjectiveSpace.CoordinateChart.dehomogenization (R := k) 1 i Equiv.ulift.symm
      (HomogeneousLocalization.mk t))) ∈ (IsLocalRing.closedPoint k).asIdeal
  have hratio : HomogeneousLocalization.mk t =
      ProjectiveSpace.affineChartHom (R := k) 1 i Equiv.ulift.symm (MvPolynomial.X (ULift.up 0)) := by
    simp only [ProjectiveSpace.affineChartHom_X]
    apply HomogeneousLocalization.val_injective (Submonoid.powers (coordinate k i))
    simp [t, ProjectiveSpace.coordinateRatio, HomogeneousLocalization.Away.isLocalizationElem,
      HomogeneousLocalization.val_mk, HomogeneousLocalization.Away.val_mk]
  rw [hratio]
  have hd := RingHom.congr_fun
    (ProjectiveSpace.CoordinateChart.dehomogenization_comp_affineChartHom
      (R := k) 1 i Equiv.ulift.symm) (MvPolynomial.X (ULift.up 0))
  change ProjectiveSpace.CoordinateChart.dehomogenization (R := k) 1 i Equiv.ulift.symm
    (ProjectiveSpace.affineChartHom (R := k) 1 i Equiv.ulift.symm
      (MvPolynomial.X (ULift.up 0))) = MvPolynomial.X (ULift.up 0) at hd
  rw [hd]
  simp

/-- The support of `twoPointDivisor k` contains the two distinct closed points `0` and `∞`. -/
theorem twoPointDivisor_spec :
    zeroPoint k ∈ (twoPointDivisor k).support ∧
      infinityPoint k ∈ (twoPointDivisor k).support := by
  have hz : zeroPoint k ∈ zeroLocus k := by
    change {y k} ⊆ ((zeroPoint k).asHomogeneousIdeal : Set (MvPolynomial (Fin 2) k))
    simpa [Set.singleton_subset_iff, zeroPoint, zeroSection, Category.assoc] using
      zeroOnChart_coordinate_mem k 0
  have hi : infinityPoint k ∈ infinityLocus k := by
    change {x k} ⊆ ((infinityPoint k).asHomogeneousIdeal : Set (MvPolynomial (Fin 2) k))
    simpa [Set.singleton_subset_iff, infinityPoint, infinitySection, Category.assoc] using
      zeroOnChart_coordinate_mem k 1
  rw [twoPointDivisor_eq]
  change zeroPoint k ∈ ((vanishingIdeal (zeroLocus k ⊔ infinityLocus k)).support : Set (scheme k)) ∧
    infinityPoint k ∈ ((vanishingIdeal (zeroLocus k ⊔ infinityLocus k)).support : Set (scheme k))
  rw [coe_support_vanishingIdeal]
  exact ⟨Or.inl hz, Or.inr hi⟩

/-- The two-point closed subscheme is an effective Cartier divisor on `ℙ¹_k`. -/
instance instIsEffectiveCartierDivisor_twoPointDivisor :
    IsEffectiveCartierDivisor (twoPointDivisor k).subschemeι := sorry

/-- The invertible sheaf `L = I_Z` associated to the ideal sheaf of `{0, ∞}`. -/
@[reducible]
def lineBundle : (scheme k).Modules :=
  (twoPointDivisor k).toModule

/-- `lineBundle k` is the module sheaf of the ideal of `{0, ∞}`. -/
theorem lineBundle_def : lineBundle k = (twoPointDivisor k).toModule := by
  rfl

/-- The canonical complex `0 → I_Z → 𝒪 → i_* 𝒪_Z → 0` on `ℙ¹_k`. -/
def idealSequence : ShortComplex (scheme k).Modules :=
  ShortComplex.mk (twoPointDivisor k).toSubobject.arrow
    (SheafOfModules.unitToPushforwardObjUnit (twoPointDivisor k).subschemeι.toRingCatSheafHom)
    (twoPointDivisor k).toSubobject_arrow_comp_quotient

/-- The first term of `idealSequence k` is `lineBundle k`. -/
theorem idealSequence_X₁ : (idealSequence k).X₁ = lineBundle k := by
  rfl

/-- The middle term of `idealSequence k` is the structure module of `ℙ¹_k`. -/
theorem idealSequence_X₂ :
    (idealSequence k).X₂ = (SheafOfModules.unit (scheme k).ringCatSheaf : (scheme k).Modules) := by
  rfl

/-- The third term of `idealSequence k` is the pushforward `i_* 𝒪_Z`. -/
theorem idealSequence_X₃ :
    (idealSequence k).X₃ = closedSubschemeStructureSheafOn (twoPointDivisor k) := by
  rfl

/-- The ideal sequence of `{0, ∞}` is short exact. -/
theorem idealSequence_shortExact : (idealSequence k).ShortExact := by
  haveI : Mono (idealSequence k).f := by
    change Mono (twoPointDivisor k).toSubobject.arrow
    infer_instance
  haveI : Epi (idealSequence k).g := by
    apply Functor.epi_of_epi_map (SheafOfModules.toSheaf (scheme k).ringCatSheaf)
    haveI : Sheaf.IsLocallySurjective
        ((SheafOfModules.toSheaf (scheme k).ringCatSheaf).map (idealSequence k).g) := by
      apply (TopCat.Presheaf.isLocallySurjective_iff _).2
      intro U t z hz
      obtain ⟨_, ⟨V, hV, rfl⟩, hzV, hVU⟩ :=
        (scheme k).isBasis_affineOpens.exists_subset_of_mem_open hz U.isOpen
      obtain ⟨s, hs⟩ := (twoPointDivisor k).subschemeι.app_surjective V hV
        (((SheafOfModules.toSheaf (scheme k).ringCatSheaf).obj
          (closedSubschemeStructureSheafOn (twoPointDivisor k))).obj.map
          (homOfLE hVU).op t)
      exact ⟨V, hVU, ⟨s, hs⟩, hzV⟩
    exact Sheaf.epi_of_isLocallySurjective _
  refine { exact := ?_ }
  apply ShortComplex.exact_of_f_is_kernel
  change IsLimit (KernelFork.ofι (kernelSubobject (idealSequence k).g).arrow _)
  apply KernelFork.IsLimit.ofι'
  intro A a ha
  refine ⟨factorThruKernelSubobject (C := (scheme k).Modules) (idealSequence k).g a ha, ?_⟩
  exact factorThruKernelSubobject_comp_arrow (C := (scheme k).Modules) (idealSequence k).g a ha

/-- The standard affine charts `D₊(x)` and `D₊(y)` of `ℙ¹_k`. -/
private abbrev twoPointChart : Fin 2 → (scheme k).Opens :=
  fun i ↦ ProjectiveSpace.coordinateBasicOpen (R := k) 1 i

/-- The inclusions of the standard charts into the top open of `ℙ¹_k`. -/
private abbrev twoPointChartι (i : Fin 2) : twoPointChart k i ⟶ (⊤ : (scheme k).Opens) :=
  homOfLE le_top

/-- The two standard charts cover `ℙ¹_k` in the Zariski topology. -/
private theorem twoPointChart_cover_mem :
    Sieve.ofArrows (twoPointChart k) (twoPointChartι k) ∈
      Opens.grothendieckTopology (scheme k) (⊤ : (scheme k).Opens) := by
  intro z hz
  have hz' : z ∈ chartX k ⊔ chartY k := by
    rw [charts_cover]
    exact hz
  rcases hz' with hzX | hzY
  · exact ⟨twoPointChart k 0, twoPointChartι k 0,
      Sieve.ofArrows_mk _ _ (0 : Fin 2), hzX⟩
  · exact ⟨twoPointChart k 1, twoPointChartι k 1,
      Sieve.ofArrows_mk _ _ (1 : Fin 2), hzY⟩

/-- The additive sheaf `i_* 𝒪_Z` on `ℙ¹_k`. -/
private abbrev twoPointSheaf :=
  (SheafOfModules.toSheaf (scheme k).ringCatSheaf).obj
    (closedSubschemeStructureSheafOn (twoPointDivisor k))

/-- The quotient sheaf has a unique section on an open contained in both standard charts. -/
private theorem twoPointSheaf_subsingleton {W : (scheme k).Opens}
    (hWX : W ≤ chartX k) (hWY : W ≤ chartY k) :
    Subsingleton ((twoPointSheaf k).obj.obj (op W)) := by
  change Subsingleton Γ((twoPointDivisor k).subscheme, (twoPointDivisor k).subschemeι ⁻¹ᵁ W)
  have hs : ((twoPointDivisor k).support : Set (scheme k)) =
      ((zeroLocus k ⊔ infinityLocus k) : Set (scheme k)) := by
    rw [twoPointDivisor_eq, coe_support_vanishingIdeal]
    rfl
  have hW : (twoPointDivisor k).subschemeι ⁻¹ᵁ W = ⊥ := by
    apply bot_unique
    intro z hz
    have hsupport : (twoPointDivisor k).subschemeι z ∈
        ((twoPointDivisor k).support : Set (scheme k)) := by
      rw [← range_subschemeι]
      exact ⟨z, rfl⟩
    rw [hs] at hsupport
    rcases hsupport with hzero | hinfty
    · have hy : y k ∉ ((twoPointDivisor k).subschemeι z).asHomogeneousIdeal := hWY hz
      exact hy (hzero (Set.mem_singleton _))
    · have hx : x k ∉ ((twoPointDivisor k).subschemeι z).asHomogeneousIdeal := hWX hz
      exact hx (hinfty (Set.mem_singleton _))
  rw [hW]
  infer_instance

/-- The unit section of `i_* 𝒪_{V(y)}`. -/
def unitOnZero :
    Hom.globalSectionsMod (toSpec k)
      (closedSubschemeStructureSheafOn (vanishingIdeal (zeroLocus k))) :=
  (SheafOfModules.pushforwardSections
      (vanishingIdeal (zeroLocus k)).subschemeι.toRingCatSheafHom
      (RingedSpace.unitSectionFromTop
        (vanishingIdeal (zeroLocus k)).subscheme.toRingedSpace
        (RingedSpace.unitTopValue
          (vanishingIdeal (zeroLocus k)).subscheme.toRingedSpace))).1 (op ⊤)

/-- The local section of `i_* 𝒪_Z` that is `1` on `chartX ∩ Z` and `0` on `chartY ∩ Z`. -/
private def indicatorZeroOnChart (i : Fin 2) :
    (twoPointSheaf k).obj.obj (op (twoPointChart k i)) :=
  if i = 0 then
    (SheafOfModules.unitToPushforwardObjUnit
        (twoPointDivisor k).subschemeι.toRingCatSheafHom).val.app
      (op (twoPointChart k i)) (1 : Γ(scheme k, twoPointChart k i))
  else
    0

/-- The local morphisms `ℤ ⟶ (i_* 𝒪_Z)(D₊(xᵢ))` classifying `indicatorZeroOnChart`. -/
private def indicatorZeroOnChartHom (i : Fin 2) :
    AddCommGrpCat.of (ULift.{u} ℤ) ⟶
      (twoPointSheaf k).obj.obj (op (twoPointChart k i)) :=
  (AddCommGrpCat.coyonedaObjIsoForget.app
      ((twoPointSheaf k).obj.obj (op (twoPointChart k i)))).inv
    (indicatorZeroOnChart k i)

/-- The local morphisms `1` on `D₊(x)` and `0` on `D₊(y)` agree on overlaps. -/
private theorem indicatorZeroOnChartHom_compatible
    ⦃W : (scheme k).Opens⦄ ⦃i j : Fin 2⦄
    (a : W ⟶ twoPointChart k i) (b : W ⟶ twoPointChart k j)
    (hab : a ≫ twoPointChartι k i = b ≫ twoPointChartι k j) :
    indicatorZeroOnChartHom k i ≫ (twoPointSheaf k).obj.map a.op =
      indicatorZeroOnChartHom k j ≫ (twoPointSheaf k).obj.map b.op := by
  by_cases hij : i = j
  · subst j
    have hab' : a = b := Subsingleton.elim _ _
    subst b
    rfl
  · have hfin : ∀ l : Fin 2, l = 0 ∨ l = 1 :=
      Fin.forall_fin_two.mpr ⟨Or.inl rfl, Or.inr rfl⟩
    have hW : W ≤ chartX k ∧ W ≤ chartY k := by
      rcases hfin i with rfl | rfl <;> rcases hfin j with rfl | rfl
      · exact (hij rfl).elim
      · exact ⟨leOfHom a, leOfHom b⟩
      · exact ⟨leOfHom b, leOfHom a⟩
      · exact (hij rfl).elim
    letI := twoPointSheaf_subsingleton k hW.1 hW.2
    ext m
    exact Subsingleton.elim _ _

/-- The global section of `i_* 𝒪_Z` obtained by gluing value `1` on `chartX ∩ Z` and
value `0` on `chartY ∩ Z`. -/
@[no_expose]
def indicatorZero : Hom.globalSectionsMod (toSpec k) (idealSequence k).X₃ :=
  ((twoPointSheaf k).property.amalgamateOfArrows (twoPointChartι k)
      (twoPointChart_cover_mem k) (indicatorZeroOnChartHom k)
      (indicatorZeroOnChartHom_compatible k)).hom
    (ULift.up (1 : ℤ))

/-- The glued indicator has its prescribed value on each standard chart. -/
private theorem indicatorZero_restrict (i : Fin 2) :
    (twoPointSheaf k).obj.map (twoPointChartι k i).op (indicatorZero k) =
      indicatorZeroOnChart k i := by
  have h := (twoPointSheaf k).property.amalgamateOfArrows_map (twoPointChartι k)
    (twoPointChart_cover_mem k) (indicatorZeroOnChartHom k)
    (indicatorZeroOnChartHom_compatible k) i
  have h' := congrArg (fun f : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ _ ↦
    f.hom (ULift.up (1 : ℤ))) h
  change (twoPointSheaf k).obj.map (twoPointChartι k i).op (indicatorZero k) =
    (indicatorZeroOnChartHom k i).hom (ULift.up (1 : ℤ)) at h'
  rw [h']
  change (1 : ℤ) • indicatorZeroOnChart k i = indicatorZeroOnChart k i
  exact one_zsmul _

/-- Restriction to a closed component preserves the unit section. -/
private theorem closedSubschemeStructureSheafMap_one {S : Scheme.{u}}
    {I J : S.IdealSheafData} (h : I ≤ J) (U : S.Opens) :
    (closedSubschemeStructureSheafMap h).val.app (op U)
      (1 : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U)) =
        (1 : Γ(J.subscheme, J.subschemeι ⁻¹ᵁ U)) := by
  dsimp only [closedSubschemeStructureSheafMap, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply]
  have h₁ : (SheafOfModules.unitToPushforwardObjUnit
      (inclusion h).toRingCatSheafHom).val.app (op (I.subschemeι ⁻¹ᵁ U))
      (1 : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U)) =
        (1 : Γ(J.subscheme, (inclusion h) ⁻¹ᵁ (I.subschemeι ⁻¹ᵁ U))) := by
    change (inclusion h).app (I.subschemeι ⁻¹ᵁ U) 1 = 1
    exact map_one _
  change ((Modules.pushforwardCongr (inclusion_subschemeι h)).hom.app
      (SheafOfModules.unit J.subscheme.ringCatSheaf)).val.app (op U)
    (((Modules.pushforwardComp (inclusion h) I.subschemeι).hom.app
      (SheafOfModules.unit J.subscheme.ringCatSheaf)).val.app (op U)
      ((SheafOfModules.unitToPushforwardObjUnit
        (inclusion h).toRingCatSheafHom).val.app (op (I.subschemeι ⁻¹ᵁ U))
        (1 : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U)))) =
          (1 : Γ(J.subscheme, J.subschemeι ⁻¹ᵁ U))
  rw [h₁]
  change (J.subscheme.presheaf.map _).hom 1 = 1
  exact map_one _

/-- The section on the zero component is the ring unit. -/
private theorem unitOnZero_eq_one :
    unitOnZero k =
      (1 : Γ((vanishingIdeal (zeroLocus k)).subscheme,
        (vanishingIdeal (zeroLocus k)).subschemeι ⁻¹ᵁ (⊤ : (scheme k).Opens))) := by
  change ((vanishingIdeal (zeroLocus k)).subscheme.presheaf.map _).hom 1 = 1
  exact map_one _

/-- A section of an additive sheaf is determined by its values on the two standard charts. -/
private theorem twoPointSections_ext
    (F : Sheaf (Opens.grothendieckTopology (scheme k)) AddCommGrpCat.{u})
    (a b : F.obj.obj (op ⊤))
    (h : ∀ i, F.obj.map (twoPointChartι k i).op a = F.obj.map (twoPointChartι k i).op b) :
    a = b := by
  apply (AddCommGrpCat.uliftZMultiplesAddEquiv (F.obj.obj (op ⊤))).symm.injective
  apply F.property.hom_ext_ofArrows (twoPointChartι k) (twoPointChart_cover_mem k)
  intro i
  ext ⟨n⟩
  change F.obj.map (twoPointChartι k i).op (n • a) =
    F.obj.map (twoPointChartι k i).op (n • b)
  simp only [map_zsmul, h i]

/-- The structure sheaf of a reduced closed subscheme has only the zero section off its support. -/
private theorem vanishingIdeal_sections_subsingleton {S : Scheme.{u}}
    (Z : Closeds S) (U : S.Opens) (h : Disjoint (Z : Set S) (U : Set S)) :
    Subsingleton Γ((vanishingIdeal Z).subscheme, (vanishingIdeal Z).subschemeι ⁻¹ᵁ U) := by
  have hU : (vanishingIdeal Z).subschemeι ⁻¹ᵁ U = ⊥ := by
    apply bot_unique
    intro z hz
    have hZ : (vanishingIdeal Z).subschemeι z ∈ (Z : Set S) := by
      rw [← coe_support_vanishingIdeal, ← range_subschemeι]
      exact ⟨z, rfl⟩
    exact Set.disjoint_left.mp h hZ hz
  rw [hU]
  infer_instance

/-- The restrictions of `indicatorZero k` along the two closed points are `1` on `V(y)`
and `0` on `V(x)`. -/
theorem indicatorZero_spec :
    (closedSubschemeStructureSheafMap
          (inf_le_left : twoPointDivisor k ≤ vanishingIdeal (zeroLocus k))).val.app (op ⊤)
        (indicatorZero k) =
      unitOnZero k ∧
    (closedSubschemeStructureSheafMap
          (inf_le_right : twoPointDivisor k ≤ vanishingIdeal (infinityLocus k))).val.app (op ⊤)
        (indicatorZero k) =
      0 := by
  let q₀ := closedSubschemeStructureSheafMap
    (inf_le_left : twoPointDivisor k ≤ vanishingIdeal (zeroLocus k))
  let qInf := closedSubschemeStructureSheafMap
    (inf_le_right : twoPointDivisor k ≤ vanishingIdeal (infinityLocus k))
  let F₀ := (SheafOfModules.toSheaf (scheme k).ringCatSheaf).obj
    (closedSubschemeStructureSheafOn (vanishingIdeal (zeroLocus k)))
  let FInf := (SheafOfModules.toSheaf (scheme k).ringCatSheaf).obj
    (closedSubschemeStructureSheafOn (vanishingIdeal (infinityLocus k)))
  have hfin : ∀ i : Fin 2, i = 0 ∨ i = 1 :=
    Fin.forall_fin_two.mpr ⟨Or.inl rfl, Or.inr rfl⟩
  constructor
  · change q₀.val.app (op ⊤) (indicatorZero k) = unitOnZero k
    apply twoPointSections_ext k F₀
    intro i
    change (closedSubschemeStructureSheafOn (vanishingIdeal (zeroLocus k))).val.map
        (twoPointChartι k i).op (q₀.val.app (op ⊤) (indicatorZero k)) = _
    rw [← PresheafOfModules.naturality_apply]
    change q₀.val.app (op (twoPointChart k i))
        ((twoPointSheaf k).obj.map (twoPointChartι k i).op (indicatorZero k)) = _
    rw [indicatorZero_restrict]
    rcases hfin i with rfl | rfl
    · rw [unitOnZero_eq_one]
      have h₁ : indicatorZeroOnChart k 0 =
          (1 : Γ((twoPointDivisor k).subscheme,
            (twoPointDivisor k).subschemeι ⁻¹ᵁ twoPointChart k 0)) := by
        change (twoPointDivisor k).subschemeι.app (chartX k) 1 = 1
        exact map_one _
      rw [h₁]
      change q₀.val.app (op (twoPointChart k 0))
          (1 : Γ((twoPointDivisor k).subscheme,
            (twoPointDivisor k).subschemeι ⁻¹ᵁ twoPointChart k 0)) =
        ((vanishingIdeal (zeroLocus k)).subscheme.presheaf.map _).hom 1
      calc
        _ = (1 : Γ((vanishingIdeal (zeroLocus k)).subscheme,
            (vanishingIdeal (zeroLocus k)).subschemeι ⁻¹ᵁ twoPointChart k 0)) :=
          closedSubschemeStructureSheafMap_one
            (inf_le_left : twoPointDivisor k ≤ vanishingIdeal (zeroLocus k)) _
        _ = _ := (map_one _).symm
    · letI : Subsingleton (F₀.obj.obj (op (twoPointChart k 1))) :=
        vanishingIdeal_sections_subsingleton (zeroLocus k) (twoPointChart k 1) (by
          rw [Set.disjoint_left]
          intro p hp hU
          exact hU (hp (Set.mem_singleton _)))
      exact @Subsingleton.elim (F₀.obj.obj (op (twoPointChart k 1))) inferInstance _ _
  · change qInf.val.app (op ⊤) (indicatorZero k) = 0
    apply twoPointSections_ext k FInf
    intro i
    change (closedSubschemeStructureSheafOn (vanishingIdeal (infinityLocus k))).val.map
        (twoPointChartι k i).op (qInf.val.app (op ⊤) (indicatorZero k)) = _
    rw [← PresheafOfModules.naturality_apply]
    change qInf.val.app (op (twoPointChart k i))
        ((twoPointSheaf k).obj.map (twoPointChartι k i).op (indicatorZero k)) = _
    rw [indicatorZero_restrict]
    rcases hfin i with rfl | rfl
    · letI : Subsingleton (FInf.obj.obj (op (twoPointChart k 0))) :=
        vanishingIdeal_sections_subsingleton (infinityLocus k) (twoPointChart k 0) (by
          rw [Set.disjoint_left]
          intro p hp hU
          exact hU (hp (Set.mem_singleton _)))
      exact @Subsingleton.elim (FInf.obj.obj (op (twoPointChart k 0))) inferInstance _ _
    · change (qInf.val.app (op (twoPointChart k 1))).hom 0 =
        (FInf.obj.map (twoPointChartι k 1).op).hom 0
      exact (map_zero (qInf.val.app (op (twoPointChart k 1))).hom).trans
        (map_zero (FInf.obj.map (twoPointChartι k 1).op).hom).symm

/-- The connecting class `ξ ∈ H¹(ℙ¹_k, L)` of the indicator section of `i_* 𝒪_Z`. -/
def xi : Hom.cohomology (toSpec k) (lineBundle k) 1 :=
  Hom.cohomologyBoundaryFromExt (toSpec k) (idealSequence_shortExact k) (indicatorZero k)

/-- `xi k` is the Ext connecting class of `indicatorZero k`. -/
theorem xi_eq :
    xi k = Hom.cohomologyBoundaryFromExt (toSpec k) (idealSequence_shortExact k)
      (indicatorZero k) := by
  rfl

/-- The connecting class on `ℙ¹_k` is already nonzero. -/
theorem xi_ne_zero : xi k ≠ 0 := sorry

/-- The connecting class of the zero-component indicator on the projective line remains
nonzero after every finite surjective scheme morphism. -/
theorem cohomologyPullback_ne_zero {Y : Scheme.{u}} (π : Y ⟶ scheme k)
    [IsFinite π] [Surjective π] :
    Hom.cohomologyPullback (toSpec k) π (lineBundle k) 1 (xi k) ≠ 0 := sorry

end AlgebraicGeometry.ProjectiveLine.NonkillableClass
