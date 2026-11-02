/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.FieldPoint
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Point

/-!
# Homogeneous coordinates of field-valued scheme points

Coordinates are obtained by pulling back the fractions `X j / X i` on the first
standard chart containing the image of `Spec K`. The chart is found by finite
search, using a proved covering statement, rather than by inverting the admitted
classification theorem `homMk_bijective`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry LinearAlgebra.Projectivization

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

/-- Every point of standard projective space lies in a coordinate chart. -/
theorem exists_fieldPointChart {R : Type u} [CommRing R] (n : ℕ)
    (x : scheme R n) :
    ∃ i : Fin (n + 1), x ∈ Proj.basicOpen (grading R n) (MvPolynomial.X i) := by
  classical
  by_contra! hall
  apply x.not_irrelevant_le
  rw [HomogeneousIdeal.irrelevant_le]
  intro degree hdegree polynomial hpolynomial
  have hspan : Ideal.span (Set.range (MvPolynomial.X : Fin (n + 1) →
      MvPolynomial (Fin (n + 1)) R)) ≤ x.asHomogeneousIdeal.toIdeal := by
    rw [Ideal.span_le, Set.range_subset_iff]
    exact fun i ↦ not_not.mp (hall i)
  apply hspan
  have hmem : polynomial ∈ MvPolynomial.idealOfVars (Fin (n + 1)) R ^ 1 := by
    apply (MvPolynomial.mem_pow_idealOfVars_iff 1 polynomial).mpr
    intro monomial hmonomial
    have heq : monomial.degree = degree := by
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using
        hpolynomial (MvPolynomial.mem_support_iff.mp hmonomial)
    omega
  simpa only [pow_one, MvPolynomial.idealOfVars] using hmem

/-- The first standard chart containing the image of the unique point of `Spec K`. -/
def fieldPointChartIndex {R K : Type u} [CommRing R] [Field K] {n : ℕ}
    (f : Spec (CommRingCat.of K) ⟶ scheme R n) : Fin (n + 1) := by
  classical
  exact Fin.find (fun i ↦ f.base (⊥ : PrimeSpectrum K) ∈
    Proj.basicOpen (grading R n) (MvPolynomial.X i))
    (exists_fieldPointChart n (f.base (⊥ : PrimeSpectrum K)))

/-- The selected chart contains the scheme point. -/
theorem fieldPointChartIndex_mem {R K : Type u} [CommRing R] [Field K] {n : ℕ}
    (f : Spec (CommRingCat.of K) ⟶ scheme R n) :
    f.base (⊥ : PrimeSpectrum K) ∈
      Proj.basicOpen (grading R n) (MvPolynomial.X (fieldPointChartIndex f)) := by
  classical
  exact Fin.find_spec (exists_fieldPointChart n (f.base (⊥ : PrimeSpectrum K)))

/-- A coordinate fraction on a standard projective chart. -/
def fieldPointChartRatio (R : Type u) [CommRing R] (n : ℕ)
    (i j : Fin (n + 1)) :
    HomogeneousLocalization.Away (grading R n) (MvPolynomial.X i) :=
  HomogeneousLocalization.Away.isLocalizationElem
    (MvPolynomial.isHomogeneous_X R i) (MvPolynomial.isHomogeneous_X R j)

/-- The diagonal coordinate fraction is one. -/
theorem fieldPointChartRatio_self (R : Type u) [CommRing R] (n : ℕ)
    (i : Fin (n + 1)) : fieldPointChartRatio R n i i = 1 := by
  apply HomogeneousLocalization.val_injective
  simp [fieldPointChartRatio, HomogeneousLocalization.Away.isLocalizationElem,
    HomogeneousLocalization.Away.val_mk]

/-- Since `Spec K` has one point, the inverse image of the selected chart is all of it. -/
theorem fieldPointChart_preimage {R K : Type u} [CommRing R] [Field K] {n : ℕ}
    (f : Spec (CommRingCat.of K) ⟶ scheme R n) :
    ⊤ ≤ f ⁻¹ᵁ Proj.basicOpen (grading R n)
      (MvPolynomial.X (fieldPointChartIndex f)) := by
  intro point hpoint
  change f.base point ∈ Proj.basicOpen (grading R n)
    (MvPolynomial.X (fieldPointChartIndex f))
  have heq : point = (⊥ : PrimeSpectrum K) := Subsingleton.elim _ _
  simpa only [heq] using fieldPointChartIndex_mem f

/-- Evaluation in `K` of sections on the selected coordinate chart, via pullback along `f`. -/
def fieldPointChartPullback {R K : Type u} [CommRing R] [Field K] {n : ℕ}
    (f : Spec (CommRingCat.of K) ⟶ scheme R n) :
    HomogeneousLocalization.Away (grading R n)
      (MvPolynomial.X (fieldPointChartIndex f)) →+* K :=
  (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.comp
    ((f.appLE (Proj.basicOpen (grading R n)
      (MvPolynomial.X (fieldPointChartIndex f))) ⊤
        (fieldPointChart_preimage f)).hom.comp
      (Proj.awayToSection (grading R n)
        (MvPolynomial.X (fieldPointChartIndex f))).hom)

/-- A homogeneous tuple, normalized to one in the selected chart. -/
def fieldPointCoordinateTuple {R K : Type u} [CommRing R] [Field K] {n : ℕ}
    (f : Spec (CommRingCat.of K) ⟶ scheme R n) : Fin (n + 1) → K :=
  fun j ↦ fieldPointChartPullback f (fieldPointChartRatio R n (fieldPointChartIndex f) j)

/-- The selected homogeneous coordinate is one. -/
theorem fieldPointCoordinateTuple_index {R K : Type u} [CommRing R] [Field K] {n : ℕ}
    (f : Spec (CommRingCat.of K) ⟶ scheme R n) :
    fieldPointCoordinateTuple f (fieldPointChartIndex f) = 1 := by
  simp [fieldPointCoordinateTuple, fieldPointChartRatio_self]

/-- The tuple read from a scheme point is nonzero. -/
theorem fieldPointCoordinateTuple_ne_zero {R K : Type u} [CommRing R] [Field K] {n : ℕ}
    (f : Spec (CommRingCat.of K) ⟶ scheme R n) : fieldPointCoordinateTuple f ≠ 0 := by
  intro heq
  have hone := fieldPointCoordinateTuple_index f
  rw [heq, Pi.zero_apply] at hone
  exact zero_ne_one hone

/-- On a tuple-defined point, chart pullback is division by the selected coordinate. -/
theorem fieldPointCoordinateTuple_homOf {R K : Type u} [CommRing R] [Field K]
    (φ : R →+* K) (n : ℕ) {v : Fin (n + 1) → K} (hv : v ≠ 0)
    (j : Fin (n + 1)) :
    fieldPointCoordinateTuple (homOf φ hv) j =
      v j / v (fieldPointChartIndex (homOf φ hv)) := sorry

/-- The coordinate class of an over-base field-valued point. -/
def coordinates {R K : Type u} [CommRing R] [Field K] (φ : R →+* K) (n : ℕ)
    (f : Over.mk (Spec.map (CommRingCat.ofHom φ)) ⟶ schemeOver R n) :
    ℙ K (Fin (n + 1) → K) :=
  Projectivization.mk K (fieldPointCoordinateTuple f.left)
    (fieldPointCoordinateTuple_ne_zero f.left)

/-- Reading coordinates is left inverse to the existing homogeneous constructor. -/
theorem coordinates_homMk {R K : Type u} [CommRing R] [Field K]
    (φ : R →+* K) (n : ℕ) (x : ℙ K (Fin (n + 1) → K)) :
    coordinates φ n (homMk φ n x) = x := sorry

/-- Reading coordinates is right inverse to the existing homogeneous constructor. -/
theorem homMk_coordinates {R K : Type u} [CommRing R] [Field K]
    (φ : R →+* K) (n : ℕ)
    (f : Over.mk (Spec.map (CommRingCat.ofHom φ)) ⟶ schemeOver R n) :
    homMk φ n (coordinates φ n f) = f := sorry

/-- Coordinates recover a standard representative. -/
theorem coordinates_homOf {R K : Type u} [CommRing R] [Field K]
    (φ : R →+* K) (n : ℕ) {v : Fin (n + 1) → K} (hv : v ≠ 0) :
    coordinates φ n (Over.homMk (homOf φ hv) (homOf_isOver φ hv)) =
      Projectivization.mk K v hv := by
  rw [← homMk_mk]
  exact coordinates_homMk φ n _

/-- Coordinate classes are unchanged by unit scaling of a tuple. -/
theorem coordinates_homOf_smul {R K : Type u} [CommRing R] [Field K]
    (φ : R →+* K) (n : ℕ) {v : Fin (n + 1) → K} (hv : v ≠ 0) (t : Kˣ) :
    coordinates φ n
      (Over.homMk (homOf φ ((smul_ne_zero_iff_ne t).mpr hv))
        (homOf_isOver φ ((smul_ne_zero_iff_ne t).mpr hv))) =
      coordinates φ n (Over.homMk (homOf φ hv) (homOf_isOver φ hv)) := by
  congr 1
  apply Over.OverMorphism.ext
  exact homOf_smul φ hv t

/-- The canonical map from the chosen terminal field point to the identity-base spectrum. -/
def pointToSpec (K : Type u) [Field K] :
    SchemeOverField.point K ⟶ Over.mk (Spec.map (CommRingCat.ofHom (RingHom.id K))) :=
  Over.homMk (SchemeOverField.point K).hom (by
    simp only [CommRingCat.ofHom_id, Over.mk_hom, Spec.map_id]
    exact Category.comp_id _)

/-- The map from the identity-base spectrum to the chosen terminal field point. -/
def specToPoint (K : Type u) [Field K] :
    Over.mk (Spec.map (CommRingCat.ofHom (RingHom.id K))) ⟶ SchemeOverField.point K :=
  (SchemeOverField.pointIsTerminal K).from _

/-- The two explicit changes of field-point source cancel at the spectrum. -/
theorem specToPoint_pointToSpec (K : Type u) [Field K] :
    specToPoint K ≫ pointToSpec K = 𝟙 _ := by
  apply Over.OverMorphism.ext
  change (specToPoint K).left ≫ (SchemeOverField.point K).hom =
    𝟙 (Spec (CommRingCat.of K))
  simpa only [CommRingCat.ofHom_id, Over.mk_hom, Spec.map_id] using (specToPoint K).w

/-- The two changes of source cancel at the chosen terminal point. -/
theorem pointToSpec_specToPoint (K : Type u) [Field K] :
    pointToSpec K ≫ specToPoint K = 𝟙 _ :=
  (SchemeOverField.pointIsTerminal K).hom_ext _ _

/-- The existing homogeneous constructor, with the chosen field-point source. -/
def pointHomMk {K : Type u} [Field K] (n : ℕ) (x : ℙ K (Fin (n + 1) → K)) :
    SchemeOverField.point K ⟶ schemeOver K n :=
  pointToSpec K ≫ homMk (RingHom.id K) n x

/-- Coordinates of a projective point whose source is the chosen terminal field point. -/
def pointCoordinates {K : Type u} [Field K] (n : ℕ)
    (f : SchemeOverField.point K ⟶ schemeOver K n) : ℙ K (Fin (n + 1) → K) :=
  coordinates (RingHom.id K) n (specToPoint K ≫ f)

/-- The terminal-source coordinate map recovers a homogeneous class. -/
theorem pointCoordinates_pointHomMk {K : Type u} [Field K] (n : ℕ)
    (x : ℙ K (Fin (n + 1) → K)) :
    pointCoordinates n (pointHomMk n x) = x := by
  unfold pointCoordinates pointHomMk
  rw [← Category.assoc, specToPoint_pointToSpec, Category.id_comp, coordinates_homMk]

/-- The terminal-source homogeneous constructor recovers a scheme point. -/
theorem pointHomMk_pointCoordinates {K : Type u} [Field K] (n : ℕ)
    (f : SchemeOverField.point K ⟶ schemeOver K n) :
    pointHomMk n (pointCoordinates n f) = f := by
  unfold pointHomMk pointCoordinates
  rw [homMk_coordinates, ← Category.assoc, pointToSpec_specToPoint, Category.id_comp]

end AlgebraicGeometry.ProjectiveSpace
