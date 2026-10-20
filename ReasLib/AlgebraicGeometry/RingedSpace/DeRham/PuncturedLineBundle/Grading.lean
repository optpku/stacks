/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.PuncturedLineBundle.TensorAction
public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.PuncturedLineBundle.Weights

/-! Canonical geometric homogeneous pieces and their comparison morphisms.
No caller-supplied grading, multiplication or restriction map is accepted. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory ComplexShape AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.DeRham.PuncturedLineBundle

variable {S X : Scheme.{u}} (f : X ⟶ S) (ℒ : X.Modules)
variable [Scheme.Modules.Invertible ℒ]
variable (P : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra ℒ))
variable [Scheme.IsRelativeSpectrumOver P]

/-- Inclusion of the canonically generated punctured homogeneous forms. -/
def puncturedFormInclusion (p : ℕ) (n : ℤ) :
    puncturedForm f ℒ P p n ⟶ puncturedAmbientForm f ℒ P p :=
  ⟨(puncturedPiece f ℒ P p n).arrow⟩

/-- Inclusion of the canonically generated polynomial homogeneous forms. -/
def totalFormInclusion (p n : ℕ) :
    totalForm f ℒ P p n ⟶ totalAmbientForm f ℒ P p :=
  ⟨(totalPiece f ℒ P p n).arrow⟩

/-- Multiply weight-zero forms by powers of the tautological trivialization. -/
def puncturedMultiplication (p : ℕ) (n : ℤ) :
    Scheme.Modules.twistByTensorPower ℒ (puncturedForm f ℒ P p 0).obj n ⟶
      (puncturedAmbientForm f ℒ P p).obj :=
  ((puncturedPiece f ℒ P p 0).arrow ▷ Scheme.Modules.tensorPowerInt ℒ n) ≫
    (puncturedPowerAction f ℒ P p n).hom

/-- Multiplication by a degree-n line power carries weight-zero generators into weight n. -/
theorem puncturedMultiplication_factors (p : ℕ) (n : ℤ) :
    (puncturedPiece f ℒ P p n).Factors (puncturedMultiplication f ℒ P p n) := sorry

/-- Factorization of actual geometric multiplication through the homogeneous subobject. -/
def twistComparison (p : ℕ) (n : ℤ) :
    Scheme.QCoh.twistByTensorPower ℒ (puncturedForm f ℒ P p 0) n ⟶
      puncturedForm f ℒ P p n :=
  ⟨(puncturedPiece f ℒ P p n).factorThru (puncturedMultiplication f ℒ P p n)
    (puncturedMultiplication_factors f ℒ P p n)⟩

/-- The factorization recovers geometric multiplication. -/
theorem twistComparison_def (p : ℕ) (n : ℤ) :
    (twistComparison f ℒ P p n).hom ≫ (puncturedPiece f ℒ P p n).arrow =
      puncturedMultiplication f ℒ P p n :=
  Subobject.factorThru_arrow _ _ (puncturedMultiplication_factors f ℒ P p n)

/-- The generated-subobject inclusion uniquely determines the comparison. -/
theorem twistComparison_unique (p : ℕ) (n : ℤ)
    (g : Scheme.Modules.twistByTensorPower ℒ (puncturedForm f ℒ P p 0).obj n ⟶
      (puncturedForm f ℒ P p n).obj)
    (hg : g ≫ (puncturedPiece f ℒ P p n).arrow = puncturedMultiplication f ℒ P p n) :
    g = (twistComparison f ℒ P p n).hom := by
  apply (cancel_mono (puncturedPiece f ℒ P p n).arrow).mp
  exact hg.trans (twistComparison_def f ℒ P p n).symm

set_option backward.isDefEq.respectTransparency false in
/-- A zero comparison is possible only when the actual geometric multiplication is zero;
the old arbitrary-zero-multiplication grading cannot be supplied to this interface. -/
theorem twistComparison_eq_zero_iff (p : ℕ) (n : ℤ) :
    (twistComparison f ℒ P p n).hom = 0 ↔ puncturedMultiplication f ℒ P p n = 0 := by
  constructor
  · intro h
    rw [← twistComparison_def f ℒ P p n, h, zero_comp]
  · intro h
    apply (cancel_mono (puncturedPiece f ℒ P p n).arrow).mp
    rw [twistComparison_def, h, zero_comp]

/-- Restricting homogeneous polynomial forms preserves their weight. -/
theorem restriction_factors (p n : ℕ) :
    (puncturedPiece f ℒ P p (n : ℤ)).Factors
      ((totalPiece f ℒ P p n).arrow ≫ restrictionAlongPuncturedOpen f ℒ P p) := sorry

/-- Actual restriction between homogeneous pieces. The map exists at weight zero too;
only its isomorphism theorem requires positive weight. -/
def positiveWeightComparison (p n : ℕ) :
    totalForm f ℒ P p n ⟶ puncturedForm f ℒ P p (n : ℤ) :=
  ⟨(puncturedPiece f ℒ P p (n : ℤ)).factorThru
    ((totalPiece f ℒ P p n).arrow ≫ restrictionAlongPuncturedOpen f ℒ P p)
    (restriction_factors f ℒ P p n)⟩

/-- The homogeneous restriction has exactly the actual open-restriction composite. -/
theorem positiveWeightComparison_def (p n : ℕ) :
    (positiveWeightComparison f ℒ P p n).hom ≫
        (puncturedPiece f ℒ P p (n : ℤ)).arrow =
      (totalPiece f ℒ P p n).arrow ≫ restrictionAlongPuncturedOpen f ℒ P p :=
  Subobject.factorThru_arrow _ _ (restriction_factors f ℒ P p n)

/-- The actual pushed-forward total-space de Rham complex in nonnegative degrees. -/
abbrev totalAmbientComplexNat : CochainComplex (Modules f.toShHom) ℕ :=
  (RingedSpace.DeRham.pushforwardComplex (totalDeRhamSquare f ℒ P)).obj
    (RingedSpace.DeRham.complex (P.π ≫ f).toShHom)

/-- Inclusion of a generated weight piece, with coefficients restricted to the base.
The section function is precisely the original generated-subobject inclusion. -/
def totalTermInclusion (p n : ℕ) :
    (restrictToBaseModules f).obj (totalForm f ℒ P p n).obj ⟶
      (totalAmbientComplexNat f ℒ P).X p where
  val :=
    { app := fun U => ModuleCat.ofHom
        (R := (RingedSpace.DeRham.coefficients f.toShHom).obj.obj U)
        (X := ((restrictToBaseModules f).obj (totalForm f ℒ P p n).obj).val.obj U)
        (Y := ((totalAmbientComplexNat f ℒ P).X p).val.obj U)
        { toFun := fun m => (totalPiece f ℒ P p n).arrow.val.app U m
          map_add' := by sorry
          map_smul' := by sorry }
      naturality := by sorry }

/-- Restricting scalars preserves injectivity of the generated-subobject inclusion. -/
instance totalTermInclusion_mono (p n : ℕ) : Mono (totalTermInclusion f ℒ P p n) :=
  by sorry

/-- The geometric weight piece as a subobject of the actual de Rham term. -/
def totalTermPiece (p n : ℕ) : Subobject ((totalAmbientComplexNat f ℒ P).X p) :=
  Subobject.mk (totalTermInclusion f ℒ P p n)

/-- The de Rham differential preserves the sum of the weights of its homogeneous factors. -/
theorem totalDifferential_factors (p n : ℕ) :
    (totalTermPiece f ℒ P (p + 1) n).Factors
      ((totalTermPiece f ℒ P p n).arrow ≫ (totalAmbientComplexNat f ℒ P).d p (p + 1)) :=
  sorry

/-- The differential of a weight piece is the restriction of the real de Rham differential. -/
def totalWeightDifferential (p n : ℕ) :
    (totalTermPiece f ℒ P p n : Modules f.toShHom) ⟶
      (totalTermPiece f ℒ P (p + 1) n : Modules f.toShHom) :=
  (totalTermPiece f ℒ P (p + 1) n).factorThru
    ((totalTermPiece f ℒ P p n).arrow ≫ (totalAmbientComplexNat f ℒ P).d p (p + 1))
    (totalDifferential_factors f ℒ P p n)

/-- The weight differential is determined by its composite with the actual inclusion. -/
theorem totalWeightDifferential_inclusion (p n : ℕ) :
    totalWeightDifferential f ℒ P p n ≫ (totalTermPiece f ℒ P (p + 1) n).arrow =
      (totalTermPiece f ℒ P p n).arrow ≫ (totalAmbientComplexNat f ℒ P).d p (p + 1) :=
  Subobject.factorThru_arrow _ _ (totalDifferential_factors f ℒ P p n)

/-- The restricted differential squares to zero, by cancellation of the inclusion. -/
theorem totalWeightDifferential_sq (p n : ℕ) :
    totalWeightDifferential f ℒ P p n ≫ totalWeightDifferential f ℒ P (p + 1) n = 0 := by
  apply (cancel_mono (totalTermPiece f ℒ P (p + 1 + 1) n).arrow).mp
  rw [Category.assoc, totalWeightDifferential_inclusion,
    ← Category.assoc, totalWeightDifferential_inclusion, Category.assoc]
  rw [HomologicalComplex.d_comp_d, comp_zero, zero_comp]

/-- The total-space weight complex, constructed independently from geometric generators. -/
def totalWeightComplexNat (n : ℕ) : CochainComplex (Modules f.toShHom) ℕ :=
  CochainComplex.of (fun p => (totalTermPiece f ℒ P p n : Modules f.toShHom))
    (fun p => totalWeightDifferential f ℒ P p n)
    (fun p => totalWeightDifferential_sq f ℒ P p n)

/-- The term identification comes from the actual generated-subobject inclusion. -/
def totalWeightTermIso (p n : ℕ) :
    (totalWeightComplexNat f ℒ P n).X p ≅
      (restrictToBaseModules f).obj (totalForm f ℒ P p n).obj :=
  Subobject.underlyingIso (totalTermInclusion f ℒ P p n)

/-- The term identification commutes with the geometric inclusion, ruling out an unrelated
isomorphism between objects with different embeddings. -/
theorem totalWeightTermIso_inclusion (p n : ℕ) :
    (totalWeightTermIso f ℒ P p n).inv ≫ (totalTermPiece f ℒ P p n).arrow =
      totalTermInclusion f ℒ P p n :=
  Subobject.underlyingIso_arrow _

/-- Termwise generated-subobject inclusions assemble to the actual subcomplex inclusion. -/
def totalWeightInclusionNat (n : ℕ) :
    totalWeightComplexNat f ℒ P n ⟶ totalAmbientComplexNat f ℒ P :=
  CochainComplex.ofHom (fun p => (totalTermPiece f ℒ P p n).arrow) (fun p => by
    change _ = CochainComplex.of.d _ _ p (p + 1) ≫ _
    rw [CochainComplex.of_d]
    exact (totalWeightDifferential_inclusion f ℒ P p n).symm)

/-- The total homogeneous de Rham complex, extended by zero to negative form degrees. -/
def totalWeightComplex (n : ℕ) : CochainComplex (Modules f.toShHom) ℤ :=
  (totalWeightComplexNat f ℒ P n).extend embeddingUpNat

/-- The actual generated weight-zero subcomplex; it is not defined as the image of the
comparison whose isomorphism is to be asserted. -/
abbrev totalDegreeZeroComplex := totalWeightComplex f ℒ P 0

/-- The inclusion into the total-space de Rham complex. -/
def totalDegreeZeroInclusion :
    totalDegreeZeroComplex f ℒ P ⟶ totalPushedForwardDeRham f ℒ P :=
  HomologicalComplex.extendMap (totalWeightInclusionNat f ℒ P 0) embeddingUpNat

/-- Ordinary forms have geometric weight zero under pullback to the total line bundle. -/
theorem ordinary_factors (p : ℕ) :
    (totalTermPiece f ℒ P p 0).Factors
      ((RingedSpace.DeRham.map (totalDeRhamSquare f ℒ P)).f p) := sorry

/-- The ordinary comparison degreewise, factored through independently generated pieces. -/
def degreeZeroComparisonNat :
    RingedSpace.DeRham.complex f.toShHom ⟶ totalWeightComplexNat f ℒ P 0 :=
  CochainComplex.ofHom (fun p => (totalTermPiece f ℒ P p 0).factorThru
    ((RingedSpace.DeRham.map (totalDeRhamSquare f ℒ P)).f p)
    (ordinary_factors f ℒ P p)) (fun p => by
      simp only [totalWeightComplexNat, CochainComplex.of_d]
      apply (cancel_mono (totalTermPiece f ℒ P (p + 1) 0).arrow).mp
      rw [Category.assoc, totalWeightDifferential_inclusion,
        ← Category.assoc, Subobject.factorThru_arrow, Category.assoc,
        Subobject.factorThru_arrow]
      exact (RingedSpace.DeRham.map (totalDeRhamSquare f ℒ P)).comm p (p + 1))

/-- The degree-zero comparison is the actual functorial pullback with its range restricted. -/
def degreeZeroComparison : ordinaryComplex f ⟶ totalDegreeZeroComplex f ℒ P :=
  HomologicalComplex.extendMap (degreeZeroComparisonNat f ℒ P) embeddingUpNat

/-- At every nonnegative degree the comparison followed by inclusion is ordinary pullback. -/
theorem degreeZeroComparisonNat_inclusion (p : ℕ) :
    (degreeZeroComparisonNat f ℒ P).f p ≫ (totalTermPiece f ℒ P p 0).arrow =
      ((RingedSpace.DeRham.map (totalDeRhamSquare f ℒ P)).f p) :=
  Subobject.factorThru_arrow _ _ (ordinary_factors f ℒ P p)

/-- The comparison into the weight-zero subcomplex recovers the genuine pullback of complexes. -/
theorem degreeZeroComparison_def :
    degreeZeroComparison f ℒ P ≫ totalDegreeZeroInclusion f ℒ P =
      ordinaryToTotalPushedForward f ℒ P := by
  change HomologicalComplex.extendMap (degreeZeroComparisonNat f ℒ P) embeddingUpNat ≫
    HomologicalComplex.extendMap (totalWeightInclusionNat f ℒ P 0) embeddingUpNat = _
  rw [← HomologicalComplex.extendMap_comp]
  congr 1
  ext p : 1
  exact degreeZeroComparisonNat_inclusion f ℒ P p

end AlgebraicGeometry.RingedSpace.DeRham.PuncturedLineBundle
