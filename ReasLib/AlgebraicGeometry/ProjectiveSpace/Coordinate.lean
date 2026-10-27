/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Standard projective coordinates

The coordinate charts of standard projective space are described through homogeneous
localizations and identified explicitly with affine space.

The standard covering and its affine chart isomorphisms are described in Stacks Tag `01NG`.
Affineness of projective standard opens is Tag `01MB`, and their rings of sections are
identified in Tag `01M7`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u v

namespace AlgebraicGeometry.ProjectiveSpace

section

variable {R : Type u} [CommRing R]

/-- The basic open `D₊(f)` in standard projective space for the standard polynomial grading. -/
abbrev basicOpen (n : ℕ) (f : MvPolynomial (Fin (n + 1)) R) :
    (scheme R n).Opens :=
  Proj.basicOpen (grading R n) f

/-- A standard projective-space basic open is affine when its defining polynomial is
homogeneous of positive degree. -/
@[stacks 01MB "projective basic-open affineness"]
theorem basicOpen_isAffineOpen (n : ℕ) (f : MvPolynomial (Fin (n + 1)) R)
    (d : ℕ) (hf : f ∈ grading R n d) (hd : 0 < d) :
    IsAffineOpen (basicOpen n f) :=
  Proj.isAffineOpen_basicOpen (grading R n) f hf hd

/-- The homogeneous coordinate `T_i` on standard projective `n`-space. -/
abbrev coordinate (n : ℕ) (i : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) R :=
  MvPolynomial.X i

/-- The coordinate polynomial `T_i` has degree `1` in the standard grading on
`R[T_0, ..., T_n]`. -/
theorem coordinate_mem_grading_one (n : ℕ) (i : Fin (n + 1)) :
    coordinate (R := R) n i ∈ grading R n 1 := sorry

/-- The standard chart `D₊(T_i)` on `scheme R n` is affine. -/
@[stacks 01MB "projective coordinate chart affineness"]
theorem coordinateBasicOpen_isAffineOpen (n : ℕ) (i : Fin (n + 1)) :
    IsAffineOpen (basicOpen (R := R) n (coordinate (R := R) n i)) :=
  Proj.isAffineOpen_basicOpen (grading R n) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one

/-- The standard affine chart `D₊(T_i)` on `scheme R n`. -/
@[stacks 01NG "projective coordinate chart"]
abbrev coordinateBasicOpen (n : ℕ) (i : Fin (n + 1)) :
    (scheme R n).affineOpens :=
  ⟨basicOpen (R := R) n (coordinate (R := R) n i),
    Proj.isAffineOpen_basicOpen (grading R n) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one⟩

/-- The homogeneous coordinates generate the standard projective coordinate ring over its
degree-zero piece. -/
theorem coordinates_generate (n : ℕ) :
    Algebra.adjoin (grading R n 0)
      (Set.range (coordinate (R := R) n)) = ⊤ := sorry

/-- The standard affine coordinate charts cover projective space. -/
@[stacks 01NG "projective coordinate chart cover"]
theorem iSup_coordinateBasicOpen_eq_top (n : ℕ) :
    (⨆ i : Fin (n + 1),
      (coordinateBasicOpen (R := R) n i : (scheme R n).Opens)) = ⊤ := sorry

/-- The degree-zero homogeneous localization away from the coordinate `T_i`. -/
abbrev coordinateAway (n : ℕ) (i : Fin (n + 1)) :=
  HomogeneousLocalization.Away (grading R n)
    (coordinate (R := R) n i)

/-- The ordinary localization away from the coordinate `T_i`. -/
abbrev coordinateLocalizationAway (n : ℕ) (i : Fin (n + 1)) :=
  Localization.Away (coordinate (R := R) n i)

/-- The canonical map from the degree-zero localization away from `T_i` to the ordinary
localization away from `T_i`. -/
abbrev coordinateAwayToLocalization (n : ℕ) (i : Fin (n + 1)) :
    coordinateAway (R := R) n i →+* coordinateLocalizationAway (R := R) n i :=
  algebraMap (coordinateAway (R := R) n i) (coordinateLocalizationAway (R := R) n i)

/-- The canonical ring identification on the standard chart `D₊(T_i)` of `scheme R n`. -/
@[stacks 01M7 "projective coordinate chart sections"]
abbrev coordinateBasicOpenIsoAway (n : ℕ) (i : Fin (n + 1)) :
    CommRingCat.of (coordinateAway (R := R) n i) ≅
      Γ(scheme R n, (coordinateBasicOpen (R := R) n i : (scheme R n).Opens)) :=
  Proj.basicOpenIsoAway (grading R n) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one

/-- The coefficient map into the degree-zero homogeneous localization on `D₊(T_i)`. -/
abbrev coefficientToCoordinateAway (n : ℕ) (i : Fin (n + 1)) :
    R →+* coordinateAway (R := R) n i :=
  (HomogeneousLocalization.fromZeroRingHom
      (grading R n)
      (Submonoid.powers (coordinate (R := R) n i))).comp
    (algebraMap R (grading R n 0))

/-- Dehomogenization at `T_i`, sending `T_i` to `1` and the remaining coordinates through
`e : Fin n ≃ ι`. -/
noncomputable def dehomogenizeAt (n : ℕ) (i : Fin (n + 1))
    {ι : Type v} (e : Fin n ≃ ι) :
    MvPolynomial (Fin (n + 1)) R →+* MvPolynomial ι R :=
  MvPolynomial.eval₂Hom (algebraMap R (MvPolynomial ι R)) fun j ↦
    if h : j = i then 1 else
      MvPolynomial.X (e ((finSuccAboveEquiv i).symm ⟨j, h⟩))

/-- Dehomogenization at `T_i` sends the distinguished coordinate to `1`. -/
@[simp]
theorem dehomogenizeAt_coordinate_self (n : ℕ) (i : Fin (n + 1))
    {ι : Type v} (e : Fin n ≃ ι) :
    dehomogenizeAt (R := R) n i e (coordinate (R := R) n i) = 1 := by
  simp [dehomogenizeAt, coordinate]

/-- The distinguished coordinate becomes a unit under dehomogenization. -/
theorem dehomogenizeAt_coordinate_isUnit (n : ℕ) (i : Fin (n + 1))
    {ι : Type v} (e : Fin n ≃ ι) :
    IsUnit (dehomogenizeAt (R := R) n i e (coordinate (R := R) n i)) := by
  rw [dehomogenizeAt_coordinate_self]
  exact isUnit_one

/-- The chart coordinate `T_{i.succAbove (e.symm j)} / T_i` in the degree-zero homogeneous
localization. -/
noncomputable def coordinateRatio (n : ℕ) (i : Fin (n + 1))
    {ι : Type v} (e : Fin n ≃ ι) (j : ι) : coordinateAway (R := R) n i :=
  HomogeneousLocalization.Away.isLocalizationElem
    (MvPolynomial.isHomogeneous_X R i)
    (MvPolynomial.isHomogeneous_X R (i.succAbove (e.symm j)))

/-- The polynomial chart map sending `x_j` to `T_{i.succAbove (e.symm j)} / T_i`. -/
noncomputable def affineChartHom (n : ℕ) (i : Fin (n + 1))
    {ι : Type v} (e : Fin n ≃ ι) :
    MvPolynomial ι R →+* coordinateAway (R := R) n i :=
  MvPolynomial.eval₂Hom (coefficientToCoordinateAway (R := R) n i)
    (coordinateRatio (R := R) n i e)

/-- The affine chart map sends a polynomial variable to the corresponding homogeneous
coordinate ratio. -/
@[simp]
theorem affineChartHom_X (n : ℕ) (i : Fin (n + 1))
    {ι : Type v} (e : Fin n ≃ ι) (j : ι) :
    affineChartHom (R := R) n i e (MvPolynomial.X j) =
      coordinateRatio (R := R) n i e j := by
  simp [affineChartHom]

namespace CoordinateChart

/-- The explicit dehomogenization map from the coordinate chart ring to affine polynomial
coordinates. -/
noncomputable def dehomogenization (n : ℕ) (i : Fin (n + 1))
    {ι : Type v} (e : Fin n ≃ ι) :
    coordinateAway (R := R) n i →+* MvPolynomial ι R :=
  (Localization.awayLift (dehomogenizeAt (R := R) n i e)
      (coordinate (R := R) n i)
      (dehomogenizeAt_coordinate_isUnit (R := R) n i e)).comp
    (coordinateAwayToLocalization (R := R) n i)

/-- Dehomogenization after substitution of affine chart coordinates is the identity. -/
theorem dehomogenization_comp_affineChartHom (n : ℕ) (i : Fin (n + 1))
    {ι : Type v} (e : Fin n ≃ ι) :
    (dehomogenization (R := R) n i e).comp (affineChartHom (R := R) n i e) =
      RingHom.id (MvPolynomial ι R) := by
  have hl (a : MvPolynomial (Fin (n + 1)) R) (m : ℕ) :
      Localization.awayLift (dehomogenizeAt (R := R) n i e) (coordinate n i)
          (dehomogenizeAt_coordinate_isUnit n i e)
          (Localization.mk a ⟨coordinate n i ^ m, m, rfl⟩) =
        dehomogenizeAt n i e a := by
    simpa using Localization.awayLift_mk (dehomogenizeAt (R := R) n i e)
      (coordinate n i) a 1 (by simp) m
  have hl0 (a : MvPolynomial (Fin (n + 1)) R) :
      Localization.awayLift (dehomogenizeAt (R := R) n i e) (coordinate n i)
        (dehomogenizeAt_coordinate_isUnit n i e) (Localization.mk a ⟨1, 0, by simp⟩) =
          dehomogenizeAt n i e a := by
    simpa only [pow_zero] using hl a 0
  have hl1 (a : MvPolynomial (Fin (n + 1)) R) :
      Localization.awayLift (dehomogenizeAt (R := R) n i e) (coordinate n i)
        (dehomogenizeAt_coordinate_isUnit n i e)
        (Localization.mk a ⟨coordinate n i, 1, by simp⟩) =
          dehomogenizeAt n i e a := by
    simpa only [pow_one] using hl a 1
  apply MvPolynomial.ringHom_ext
  · intro r
    suffices h : Localization.awayLift (dehomogenizeAt (R := R) n i e) (coordinate n i)
        (dehomogenizeAt_coordinate_isUnit n i e)
        (Localization.mk (MvPolynomial.C r) ⟨1, 0, by simp⟩) = MvPolynomial.C r by
      simpa [affineChartHom, coefficientToCoordinateAway, dehomogenization,
        coordinateAwayToLocalization, HomogeneousLocalization.fromZeroRingHom,
        HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.val_mk] using h
    rw [hl0]
    simp [dehomogenizeAt]
  · intro j
    suffices h : Localization.awayLift (dehomogenizeAt (R := R) n i e) (coordinate n i)
        (dehomogenizeAt_coordinate_isUnit n i e)
        (Localization.mk (MvPolynomial.X (i.succAbove (e.symm j)))
          ⟨coordinate n i, 1, by simp⟩) = MvPolynomial.X j by
      simpa [affineChartHom, coordinateRatio, dehomogenization,
        coordinateAwayToLocalization, HomogeneousLocalization.Away.isLocalizationElem,
        HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk] using h
    rw [hl1]
    simp only [dehomogenizeAt, MvPolynomial.eval₂Hom_X', dif_neg (Fin.succAbove_ne _ _)]
    have he : (⟨i.succAbove (e.symm j), Fin.succAbove_ne _ _⟩ : {a // a ≠ i}) =
        finSuccAboveEquiv i (e.symm j) := rfl
    rw [he, Equiv.symm_apply_apply, Equiv.apply_symm_apply]

/-- Substitution of affine chart coordinates after dehomogenization is the identity. -/
theorem affineChartHom_comp_dehomogenization (n : ℕ) (i : Fin (n + 1))
    {ι : Type v} (e : Fin n ≃ ι) :
    (affineChartHom (R := R) n i e).comp (dehomogenization (R := R) n i e) =
      RingHom.id (coordinateAway (R := R) n i) := by
  classical
  let l := algebraMap (MvPolynomial (Fin (n + 1)) R) (coordinateLocalizationAway (R := R) n i)
  let u : coordinateLocalizationAway (R := R) n i := Localization.mk 1 ⟨coordinate n i, 1, by simp⟩
  let H := ((coordinateAwayToLocalization (R := R) n i).comp
    (affineChartHom (R := R) n i e)).comp (dehomogenizeAt (R := R) n i e)
  have hC (r : R) : H (MvPolynomial.C r) = l (MvPolynomial.C r) := by
    simp [H, dehomogenizeAt, affineChartHom, coefficientToCoordinateAway,
      coordinateAwayToLocalization, HomogeneousLocalization.fromZeroRingHom,
      HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.val_mk, l,
      ← Localization.mk_one_eq_algebraMap]
    rfl
  have hX (j : Fin (n + 1)) : H (MvPolynomial.X j) = l (MvPolynomial.X j) * u := by
    by_cases hj : j = i
    · subst j
      simp [H, dehomogenizeAt, l, u, coordinate, ← Localization.mk_one_eq_algebraMap,
        Localization.mk_mul]
    · have he : i.succAbove ((finSuccAboveEquiv i).symm ⟨j, hj⟩) = j := by
        exact congrArg Subtype.val ((finSuccAboveEquiv i).apply_symm_apply ⟨j, hj⟩)
      simp [H, dehomogenizeAt, hj, affineChartHom, coordinateRatio, he,
        coordinateAwayToLocalization, HomogeneousLocalization.Away.isLocalizationElem,
        HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk,
        l, u, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul]
  have hp (m : ℕ) (p : MvPolynomial (Fin (n + 1)) R) (hm : p.IsHomogeneous m) :
      H p = l p * u ^ m := by
    conv_lhs => rw [← p.support_sum_monomial_coeff]
    rw [map_sum]
    conv_rhs => rw [← p.support_sum_monomial_coeff, map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s hs
    have hd : s.degree = m := by
      rw [Finsupp.degree_eq_weight_one]
      exact hm (MvPolynomial.mem_support_iff.mp hs)
    simp only [MvPolynomial.monomial_eq, map_mul, hC, map_finsuppProd, map_pow, hX,
      mul_pow, Finsupp.prod_mul, ← mul_assoc]
    congr 1
    change (∏ j ∈ s.support, u ^ s j) = u ^ m
    rw [Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_apply, hd]
  apply RingHom.ext
  intro z
  obtain ⟨m, p, hm, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (grading R n)
    (MvPolynomial.isHomogeneous_X R i) z
  apply HomogeneousLocalization.val_injective (Submonoid.powers (coordinate (R := R) n i))
  change ((coordinateAwayToLocalization (R := R) n i).comp (affineChartHom n i e))
    (Localization.awayLift (dehomogenizeAt (R := R) n i e) (coordinate n i)
    (dehomogenizeAt_coordinate_isUnit n i e)
    (Localization.mk p ⟨coordinate n i ^ m, m, rfl⟩)) = _
  rw [show Localization.awayLift (dehomogenizeAt (R := R) n i e) (coordinate n i)
      (dehomogenizeAt_coordinate_isUnit n i e)
      (Localization.mk p ⟨coordinate n i ^ m, m, rfl⟩) = dehomogenizeAt n i e p by
    simpa using Localization.awayLift_mk (dehomogenizeAt (R := R) n i e)
      (coordinate n i) p 1 (by simp) m]
  change H p = _
  rw [hp m p (by simpa using hm)]
  simp [l, u, ← Localization.mk_one_eq_algebraMap, Localization.mk_pow, Localization.mk_mul,
    HomogeneousLocalization.Away.val_mk, coordinate]
  rfl


/-- The explicit ring equivalence from the degree-zero coordinate localization to affine
polynomial coordinates. -/
@[stacks 01NG "projective coordinate chart ring equivalence"]
noncomputable def ringEquiv (n : ℕ) (i : Fin (n + 1))
    {ι : Type v} (e : Fin n ≃ ι) :
    coordinateAway (R := R) n i ≃+* MvPolynomial ι R :=
  RingEquiv.ofRingHom (dehomogenization (R := R) n i e)
    (affineChartHom (R := R) n i e)
    (dehomogenization_comp_affineChartHom (R := R) n i e)
    (affineChartHom_comp_dehomogenization (R := R) n i e)

/-- The forward homomorphism of the chart-ring equivalence is dehomogenization. -/
@[simp]
theorem ringEquiv_toRingHom (n : ℕ) (i : Fin (n + 1))
    {ι : Type v} (e : Fin n ≃ ι) :
    (ringEquiv (R := R) n i e).toRingHom = dehomogenization (R := R) n i e := by
  rfl

/-- The inverse homomorphism of the chart-ring equivalence substitutes coordinate ratios. -/
@[simp]
theorem ringEquiv_symm_toRingHom (n : ℕ) (i : Fin (n + 1))
    {ι : Type v} (e : Fin n ≃ ι) :
    (ringEquiv (R := R) n i e).symm.toRingHom = affineChartHom (R := R) n i e := by
  rfl

/-- The inverse homomorphism of the explicit chart-ring equivalence, viewed in `CommRingCat`. -/
noncomputable abbrev ringComparison (n : ℕ) (i : Fin (n + 1))
    {ι : Type u} (e : Fin n ≃ ι) :
    CommRingCat.of (MvPolynomial ι R) ⟶
      CommRingCat.of (coordinateAway (R := R) n i) :=
  (ringEquiv (R := R) n i e).toCommRingCatIso.inv

/-- The underlying ring homomorphism of the chart-ring comparison is substitution by coordinate
ratios. -/
@[simp]
theorem ringComparison_hom (n : ℕ) (i : Fin (n + 1))
    {ι : Type u} (e : Fin n ≃ ι) :
    (ringComparison (R := R) n i e).hom = affineChartHom (R := R) n i e := by
  rfl

/-- The concrete identification of the `i`-th projective chart with affine space after choosing
names for the remaining coordinates. -/
@[stacks 01NG "projective coordinate chart isomorphism with reindexing"]
noncomputable def isoWith (n : ℕ) (i : Fin (n + 1))
    {ι : Type u} (e : Fin n ≃ ι) :
    (coordinateBasicOpen (R := R) n i : (scheme R n).Opens).toScheme ≅
      𝔸(ι; Spec (CommRingCat.of R)) :=
  Proj.basicOpenIsoSpec (grading R n) (coordinate (R := R) n i)
      (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one ≪≫
    (Scheme.Spec.mapIso
      ((ringEquiv (R := R) n i e).toCommRingCatIso.op)).symm ≪≫
    (AffineSpace.SpecIso ι (CommRingCat.of R)).symm

/-- The forward morphism of the concrete chart isomorphism with a chosen coordinate
reindexing. -/
noncomputable abbrev comparisonWith (n : ℕ) (i : Fin (n + 1))
    {ι : Type u} (e : Fin n ≃ ι) :
    (coordinateBasicOpen (R := R) n i : (scheme R n).Opens).toScheme ⟶
      𝔸(ι; Spec (CommRingCat.of R)) :=
  (isoWith (R := R) n i e).hom

/-- The concrete identification of the `i`-th standard projective chart with canonical affine
`n`-space. -/
@[stacks 01NG "projective coordinate chart isomorphism"]
noncomputable abbrev iso (n : ℕ) (i : Fin (n + 1)) :
    (coordinateBasicOpen (R := R) n i : (scheme R n).Opens).toScheme ≅
      𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of R)) :=
  isoWith (R := R) n i Equiv.ulift.symm

/-- The forward morphism of the concrete standard coordinate-chart isomorphism. -/
noncomputable abbrev comparison (n : ℕ) (i : Fin (n + 1)) :
    (coordinateBasicOpen (R := R) n i : (scheme R n).Opens).toScheme ⟶
      𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of R)) :=
  (iso (R := R) n i).hom

/-- The standard coordinate-chart comparison respects the structure maps to `Spec(R)`. -/
theorem comparison_toSpec (n : ℕ) (i : Fin (n + 1)) :
    comparison (R := R) n i ≫
        (𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of R)) ↘ Spec (CommRingCat.of R)) =
      (coordinateBasicOpen (R := R) n i).1.ι ≫ toSpec R n := sorry

end CoordinateChart

end

end AlgebraicGeometry.ProjectiveSpace
