module

public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.RingTheory.Localization.Away.Basic
public import ReasLib.LinearAlgebra.Matrix.GeneralLinearGroup
import Mathlib.Tactic.CrossRefAttribute

/-!
# The coordinate ring of the general linear group

This file owns the determinant localization representing invertible matrices indexed by an
arbitrary finite type. Rank-indexed APIs should specialize this owner to `Fin n`.
-/

@[expose] public section

noncomputable section

universe u v w

namespace AlgebraicGeometry.GeneralLinear

/-- The polynomial ring on the entries of an `ι × ι` matrix over `R`. -/
@[stacks 01KX "general-linear polynomial coordinate ring"]
abbrev polynomialRing (R : Type u) [CommRing R] (ι : Type w) :=
  MvPolynomial (ι × ι) R

/-- The generic `ι × ι` matrix over its polynomial coordinate ring. -/
@[stacks 01KX "generic matrix"]
noncomputable abbrev genericMatrix (R : Type u) [CommRing R] (ι : Type w) :
    Matrix ι ι (polynomialRing R ι) :=
  Matrix.mvPolynomialX ι ι R

/-- The coordinate in row `i` and column `j` of the generic matrix. -/
@[stacks 01KX "generic matrix coordinate"]
abbrev coordinate (R : Type u) [CommRing R] (ι : Type w) (i j : ι) :
    polynomialRing R ι :=
  MvPolynomial.X (i, j)

/-- The entries of the generic matrix are its polynomial coordinates. -/
@[simp]
abbrev genericMatrix_apply (R : Type u) [CommRing R] (ι : Type w) (i j : ι) :
    genericMatrix R ι i j = coordinate R ι i j :=
  Matrix.mvPolynomialX_apply ι ι R i j

/-- The determinant of the generic matrix. -/
@[stacks 01KX "generic matrix determinant"]
noncomputable abbrev determinant (R : Type u) [CommRing R] (ι : Type w)
    [Fintype ι] [DecidableEq ι] : polynomialRing R ι :=
  Matrix.det (genericMatrix R ι)

/-- The affine coordinate ring `R[xᵢⱼ, 1 / det(xᵢⱼ)]` representing invertible `ι × ι`
matrices. -/
@[stacks 01KX "general linear coordinate ring"]
noncomputable abbrev coordinateRing (R : Type u) [CommRing R] (ι : Type w)
    [Fintype ι] [DecidableEq ι] :=
  Localization.Away (determinant R ι)

/-- A generic matrix coordinate after localizing at the determinant. -/
@[stacks 01KX "localized generic matrix coordinate"]
noncomputable abbrev localizedCoordinate (R : Type u) [CommRing R] (ι : Type w)
    [Fintype ι] [DecidableEq ι] (i j : ι) : coordinateRing R ι :=
  algebraMap (polynomialRing R ι) (coordinateRing R ι) (coordinate R ι i j)

/-- The generic matrix after localizing all its entries at the determinant. -/
@[stacks 01KX "localized generic matrix"]
noncomputable abbrev localizedGenericMatrix (R : Type u) [CommRing R] (ι : Type w)
    [Fintype ι] [DecidableEq ι] : Matrix ι ι (coordinateRing R ι) :=
  (genericMatrix R ι).map (algebraMap (polynomialRing R ι) (coordinateRing R ι))

/-- The entries of the localized generic matrix are the localized coordinates. -/
@[simp]
theorem localizedGenericMatrix_apply (R : Type u) [CommRing R] (ι : Type w)
    [Fintype ι] [DecidableEq ι] (i j : ι) :
    localizedGenericMatrix R ι i j = localizedCoordinate R ι i j := sorry

/-- The determinant of the localized generic matrix is the image of the generic determinant. -/
theorem det_localizedGenericMatrix (R : Type u) [CommRing R] (ι : Type w)
    [Fintype ι] [DecidableEq ι] :
    Matrix.det (localizedGenericMatrix R ι) =
      algebraMap (polynomialRing R ι) (coordinateRing R ι) (determinant R ι) := sorry

/-- The localized generic matrix has invertible determinant. -/
theorem det_localizedGenericMatrix_isUnit (R : Type u) [CommRing R] (ι : Type w)
    [Fintype ι] [DecidableEq ι] :
    IsUnit (Matrix.det (localizedGenericMatrix R ι)) := sorry

/-- The canonical inverse of the localized generic determinant. -/
@[stacks 01KX "inverse generic determinant"]
noncomputable abbrev localizedDeterminantInverse (R : Type u) [CommRing R] (ι : Type w)
    [Fintype ι] [DecidableEq ι] : coordinateRing R ι :=
  IsLocalization.Away.invSelf (determinant R ι)

/-- The localized generic determinant multiplied by its canonical inverse is one. -/
@[simp, stacks 01KX "inverse generic determinant law"]
abbrev localizedDeterminant_mul_inverse (R : Type u) [CommRing R] (ι : Type w)
    [Fintype ι] [DecidableEq ι] :
    algebraMap (polynomialRing R ι) (coordinateRing R ι) (determinant R ι) *
      localizedDeterminantInverse R ι = 1 :=
  IsLocalization.Away.mul_invSelf (determinant R ι)

/-- The canonical nonsingular inverse of the localized generic matrix. -/
@[stacks 01KX "inverse localized generic matrix"]
noncomputable abbrev localizedGenericMatrixInverse (R : Type u) [CommRing R] (ι : Type w)
    [Fintype ι] [DecidableEq ι] : Matrix ι ι (coordinateRing R ι) :=
  (localizedGenericMatrix R ι)⁻¹

/-- The universal invertible `ι × ι` matrix over the general-linear coordinate ring. -/
@[stacks 01KX "universal general linear matrix"]
noncomputable def universalMatrix (R : Type u) [CommRing R] (ι : Type w)
    [Fintype ι] [DecidableEq ι] : Matrix.GeneralLinearGroup ι (coordinateRing R ι) :=
  Matrix.GeneralLinearGroup.mk'' (localizedGenericMatrix R ι)
    (det_localizedGenericMatrix_isUnit R ι)

/-- The entries of the universal matrix are the localized coordinate functions. -/
@[simp]
theorem universalMatrix_apply (R : Type u) [CommRing R] (ι : Type w)
    [Fintype ι] [DecidableEq ι] (i j : ι) :
    universalMatrix R ι i j = localizedCoordinate R ι i j := sorry

/-- The localized generic matrix multiplied by its canonical inverse is the identity matrix. -/
@[simp, stacks 01KX "localized generic matrix right inverse"]
abbrev localizedGenericMatrix_mul_inverse (R : Type u) [CommRing R] (ι : Type w)
    [Fintype ι] [DecidableEq ι] :
    localizedGenericMatrix R ι * localizedGenericMatrixInverse R ι = 1 :=
  (universalMatrix R ι).val_inv

/-- The canonical inverse multiplied by the localized generic matrix is the identity matrix. -/
@[simp, stacks 01KX "localized generic matrix left inverse"]
abbrev localizedGenericMatrix_inverse_mul (R : Type u) [CommRing R] (ι : Type w)
    [Fintype ι] [DecidableEq ι] :
    localizedGenericMatrixInverse R ι * localizedGenericMatrix R ι = 1 :=
  (universalMatrix R ι).inv_val

/-- Evaluate the polynomial matrix-coordinate ring along a base map and an invertible matrix. -/
@[stacks 01KX "polynomial matrix evaluation"]
def matrixEval {R : Type u} [CommRing R] {A : Type v} [CommRing A]
    (ι : Type w) [Fintype ι] [DecidableEq ι]
    (φ : R →+* A) (M : Matrix.GeneralLinearGroup ι A) : polynomialRing R ι →+* A :=
  MvPolynomial.eval₂Hom φ (fun ij ↦ M ij.1 ij.2)

/-- Matrix evaluation sends a coordinate to the corresponding matrix entry. -/
@[simp]
theorem matrixEval_coordinate {R : Type u} [CommRing R] {A : Type v} [CommRing A]
    (ι : Type w) [Fintype ι] [DecidableEq ι]
    (φ : R →+* A) (M : Matrix.GeneralLinearGroup ι A) (i j : ι) :
    matrixEval ι φ M (coordinate R ι i j) = M i j := sorry

/-- Evaluating the generic determinant at an invertible matrix gives its determinant. -/
theorem det_eq_matrixEval_determinant {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] (ι : Type w) [Fintype ι] [DecidableEq ι]
    (φ : R →+* A) (M : Matrix.GeneralLinearGroup ι A) :
    (Matrix.GeneralLinearGroup.det M : A) = matrixEval ι φ M (determinant R ι) := sorry

/-- Evaluation at an invertible matrix sends the generic determinant to a unit. -/
theorem matrixEval_determinant_isUnit {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] (ι : Type w) [Fintype ι] [DecidableEq ι]
    (φ : R →+* A) (M : Matrix.GeneralLinearGroup ι A) :
    IsUnit (matrixEval ι φ M (determinant R ι)) := sorry

namespace CoordinateRing

/-- The canonical localization map determined by an invertible matrix. Its denominator unit is
the explicit unit `Matrix.GeneralLinearGroup.det M`. -/
@[stacks 01KX "matrix evaluation on the general linear coordinate ring"]
noncomputable def homOfMatrix {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] (ι : Type w) [Fintype ι] [DecidableEq ι]
    (φ : R →+* A) (M : Matrix.GeneralLinearGroup ι A) : coordinateRing R ι →+* A :=
  IsLocalization.Away.lift (determinant R ι)
    (⟨Matrix.GeneralLinearGroup.det M, det_eq_matrixEval_determinant ι φ M⟩ :
      IsUnit (matrixEval ι φ M (determinant R ι)))

/-- The matrix-induced localization map extends polynomial evaluation. -/
@[simp]
theorem homOfMatrix_algebraMap {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] (ι : Type w) [Fintype ι] [DecidableEq ι]
    (φ : R →+* A) (M : Matrix.GeneralLinearGroup ι A) (p : polynomialRing R ι) :
    homOfMatrix ι φ M (algebraMap (polynomialRing R ι) (coordinateRing R ι) p) =
      matrixEval ι φ M p := sorry

/-- The matrix-induced localization map sends a coordinate function to the corresponding
matrix entry. -/
@[simp]
theorem homOfMatrix_localizedCoordinate {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] (ι : Type w) [Fintype ι] [DecidableEq ι]
    (φ : R →+* A) (M : Matrix.GeneralLinearGroup ι A) (i j : ι) :
    homOfMatrix ι φ M (localizedCoordinate R ι i j) = M i j := sorry

/-- The matrix-induced localization map restricts to the prescribed map from the base ring. -/
@[simp]
theorem homOfMatrix_comp_algebraMap {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] (ι : Type w) [Fintype ι] [DecidableEq ι]
    (φ : R →+* A) (M : Matrix.GeneralLinearGroup ι A) :
    (homOfMatrix ι φ M).comp (algebraMap R (coordinateRing R ι)) = φ := sorry

/-- Apply a coordinate-ring homomorphism entrywise to the universal matrix. -/
@[stacks 01KX "matrix of a general-linear coordinate-ring homomorphism"]
noncomputable def matrixOfHom {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] (ι : Type w) [Fintype ι] [DecidableEq ι]
    (ψ : coordinateRing R ι →+* A) : Matrix.GeneralLinearGroup ι A :=
  Matrix.GeneralLinearGroup.map ψ (universalMatrix R ι)

/-- The evaluated universal matrix has entries given by the images of localized coordinates. -/
@[simp]
theorem matrixOfHom_apply {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] (ι : Type w) [Fintype ι] [DecidableEq ι]
    (ψ : coordinateRing R ι →+* A) (i j : ι) :
    matrixOfHom ι ψ i j = ψ (localizedCoordinate R ι i j) := sorry

/-- Reconstructing a coordinate-ring homomorphism from its universal matrix is the identity. -/
@[simp]
theorem homOfMatrix_matrixOfHom {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] (ι : Type w) [Fintype ι] [DecidableEq ι]
    (ψ : coordinateRing R ι →+* A) :
    homOfMatrix ι (ψ.comp (algebraMap R (coordinateRing R ι)))
      (matrixOfHom ι ψ) = ψ := sorry

/-- Evaluating the coordinate-ring homomorphism induced by a matrix recovers that matrix. -/
@[simp]
theorem matrixOfHom_homOfMatrix {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] (ι : Type w) [Fintype ι] [DecidableEq ι]
    (φ : R →+* A) (M : Matrix.GeneralLinearGroup ι A) :
    matrixOfHom ι (homOfMatrix ι φ M) = M := sorry

/-- The left-inverse law for the equivalence between base-compatible coordinate-ring maps and
invertible matrices. -/
theorem homEquiv_left_inv {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] (ι : Type w) [Fintype ι] [DecidableEq ι]
    (φ : R →+* A)
    (ψ : { ψ : coordinateRing R ι →+* A //
      ψ.comp (algebraMap R (coordinateRing R ι)) = φ }) :
    (⟨homOfMatrix ι φ (matrixOfHom ι ψ.1),
      homOfMatrix_comp_algebraMap ι φ (matrixOfHom ι ψ.1)⟩ :
      { ψ : coordinateRing R ι →+* A //
        ψ.comp (algebraMap R (coordinateRing R ι)) = φ }) = ψ := sorry

/-- Base-compatible maps from the general-linear coordinate ring are canonically equivalent to
invertible matrices. -/
@[stacks 01KX "general linear coordinate-ring functor of points"]
noncomputable def homEquiv {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] (ι : Type w) [Fintype ι] [DecidableEq ι]
    (φ : R →+* A) :
    { ψ : coordinateRing R ι →+* A //
      ψ.comp (algebraMap R (coordinateRing R ι)) = φ } ≃
      Matrix.GeneralLinearGroup ι A where
  toFun ψ := matrixOfHom ι ψ.1
  invFun M := ⟨homOfMatrix ι φ M, homOfMatrix_comp_algebraMap ι φ M⟩
  left_inv := homEquiv_left_inv ι φ
  right_inv := matrixOfHom_homOfMatrix ι φ

/-- General-linear coordinate-ring maps over `φ`, evaluated on the universal matrix. -/
@[stacks 01KX "matrix of a base-compatible coordinate-ring homomorphism"]
noncomputable abbrev matrixOfHomOver {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] (ι : Type w) [Fintype ι] [DecidableEq ι]
    (φ : R →+* A) :
    { ψ : coordinateRing R ι →+* A //
      ψ.comp (algebraMap R (coordinateRing R ι)) = φ } →
      Matrix.GeneralLinearGroup ι A :=
  homEquiv ι φ

/-- Evaluation on the universal matrix bijects base-compatible coordinate-ring maps with
invertible matrices. -/
@[stacks 01KX "general linear functor of points"]
abbrev matrixOfHomOver_bijective {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] (ι : Type w) [Fintype ι] [DecidableEq ι]
    (φ : R →+* A) :
    Function.Bijective (matrixOfHomOver ι φ) :=
  (homEquiv ι φ).bijective

/-- Every invertible matrix has a unique base-compatible coordinate-ring map evaluating to it. -/
theorem existsUnique_hom {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] (ι : Type w) [Fintype ι] [DecidableEq ι]
    (φ : R →+* A) (M : Matrix.GeneralLinearGroup ι A) :
    ∃! ψ : coordinateRing R ι →+* A,
      ψ.comp (algebraMap R (coordinateRing R ι)) = φ ∧
        matrixOfHom ι ψ = M := sorry

/-- Apply an algebra homomorphism entrywise to the universal matrix. -/
@[stacks 01KX "matrix of a general-linear algebra homomorphism"]
noncomputable abbrev matrixOfAlgHom {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] [Algebra R A] (ι : Type w)
    [Fintype ι] [DecidableEq ι] (ψ : coordinateRing R ι →ₐ[R] A) :
    Matrix.GeneralLinearGroup ι A :=
  matrixOfHom ι ψ.toRingHom

/-- The matrix-induced coordinate-ring map commutes with the active algebra structures. -/
theorem homOfMatrix_commutes {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] [Algebra R A] (ι : Type w)
    [Fintype ι] [DecidableEq ι] (M : Matrix.GeneralLinearGroup ι A) (r : R) :
    homOfMatrix ι (algebraMap R A) M (algebraMap R (coordinateRing R ι) r) =
      algebraMap R A r := sorry

/-- The canonical `R`-algebra homomorphism determined by an invertible matrix. -/
@[stacks 01KX "algebra-valued general-linear point"]
noncomputable def algHomOfMatrix {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] [Algebra R A] (ι : Type w)
    [Fintype ι] [DecidableEq ι] (M : Matrix.GeneralLinearGroup ι A) :
    coordinateRing R ι →ₐ[R] A where
  toRingHom := homOfMatrix ι (algebraMap R A) M
  commutes' := homOfMatrix_commutes ι M

/-- Reconstructing an algebra homomorphism from its universal matrix is the identity. -/
@[simp]
theorem algHomOfMatrix_matrixOfAlgHom {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] [Algebra R A] (ι : Type w)
    [Fintype ι] [DecidableEq ι] (ψ : coordinateRing R ι →ₐ[R] A) :
    algHomOfMatrix ι (matrixOfAlgHom ι ψ) = ψ := sorry

/-- Evaluating the algebra homomorphism induced by a matrix recovers that matrix. -/
@[simp]
theorem matrixOfAlgHom_algHomOfMatrix {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] [Algebra R A] (ι : Type w)
    [Fintype ι] [DecidableEq ι] (M : Matrix.GeneralLinearGroup ι A) :
    matrixOfAlgHom (R := R) (A := A) ι
        (algHomOfMatrix (R := R) (A := A) ι M) = M := sorry

/-- Algebra maps from the general-linear coordinate ring are canonically equivalent to
invertible matrices. -/
@[stacks 01KX "general linear algebra-valued points"]
noncomputable def algHomEquiv {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] [Algebra R A] (ι : Type w)
    [Fintype ι] [DecidableEq ι] :
    (coordinateRing R ι →ₐ[R] A) ≃ Matrix.GeneralLinearGroup ι A where
  toFun := matrixOfAlgHom ι
  invFun := algHomOfMatrix ι
  left_inv := algHomOfMatrix_matrixOfAlgHom ι
  right_inv := matrixOfAlgHom_algHomOfMatrix ι

/-- Evaluation on the universal matrix bijects coordinate-ring algebra maps with invertible
matrices. -/
@[stacks 01KX "general linear algebra-valued points"]
abbrev matrixOfAlgHom_bijective (R : Type u) [CommRing R]
    (A : Type v) [CommRing A] [Algebra R A] (ι : Type w)
    [Fintype ι] [DecidableEq ι] :
    Function.Bijective
      (matrixOfAlgHom (R := R) (A := A) ι) :=
  (algHomEquiv (R := R) (A := A) ι).bijective

/-- Every invertible matrix over an `R`-algebra is evaluated from a unique coordinate-ring
algebra map. -/
theorem existsUnique_algHom {R : Type u} [CommRing R]
    {A : Type v} [CommRing A] [Algebra R A] (ι : Type w)
    [Fintype ι] [DecidableEq ι] (M : Matrix.GeneralLinearGroup ι A) :
    ∃! ψ : coordinateRing R ι →ₐ[R] A,
      matrixOfAlgHom ι ψ = M := sorry

end CoordinateRing

end AlgebraicGeometry.GeneralLinear
