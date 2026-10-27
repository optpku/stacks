/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.GeneralLinear.CoordinateRing
public import ReasLib.AlgebraicGeometry.PrimeSpectrum.Notation
public import ReasLib.AlgebraicGeometry.Scheme.OverSpec
import Mathlib.Tactic.CrossRefAttribute

/-!
# The general linear scheme

The general linear scheme is the determinant basic open in matrix affine space. This file also
records its functor-of-points equivalence over `Spec(R)` and proposition-valued consequences.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped PrimeSpectrum

noncomputable section

universe u

namespace AlgebraicGeometry.GeneralLinear

/-- The affine space of all `ι × ι` matrices over `R`. -/
@[stacks 01KX "matrix affine space"]
abbrev matrixSpace (R : Type u) [CommRing R] (ι : Type u) : Scheme.{u} :=
  Spec (CommRingCat.of (polynomialRing R ι))

/-- The affine scheme representing invertible `ι × ι` matrices over `R`. -/
@[stacks 01KX "general linear scheme"]
noncomputable abbrev scheme (R : Type u) [CommRing R] (ι : Type u)
    [Fintype ι] [DecidableEq ι] : Scheme.{u} :=
  Spec (CommRingCat.of (coordinateRing R ι))

/-- The determinant basic open in matrix affine space. -/
@[stacks 01KX "invertible matrix locus"]
abbrev matrixSpaceOpen (R : Type u) [CommRing R] (ι : Type u)
    [Fintype ι] [DecidableEq ι] : (matrixSpace R ι).Opens :=
  D(determinant R ι)

/-- The determinant basic open is canonically isomorphic to the localization-spectrum model of
the general linear scheme. -/
@[stacks 01KX "invertible matrix locus comparison"]
noncomputable def matrixSpaceOpenIso (R : Type u) [CommRing R] (ι : Type u)
    [Fintype ι] [DecidableEq ι] : (matrixSpaceOpen R ι).toScheme ≅ scheme R ι :=
  basicOpenIsoSpecAway (R := CommRingCat.of (polynomialRing R ι)) (determinant R ι)

/-- The canonical morphism from the general linear scheme to matrix affine space. -/
@[stacks 01KX "general-linear open immersion"]
noncomputable abbrev toMatrixSpace (R : Type u) [CommRing R] (ι : Type u)
    [Fintype ι] [DecidableEq ι] : scheme R ι ⟶ matrixSpace R ι :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (polynomialRing R ι) (coordinateRing R ι)))

/-- The general linear scheme is an open subscheme of matrix affine space. -/
instance toMatrixSpace_isOpenImmersion (R : Type u) [CommRing R] (ι : Type u)
    [Fintype ι] [DecidableEq ι] : IsOpenImmersion (toMatrixSpace R ι) := sorry

/-- Identifying the determinant basic open with the general linear scheme gives its inclusion
into matrix space. -/
@[reassoc (attr := simp)]
theorem matrixSpaceOpenIso_hom_toMatrixSpace (R : Type u) [CommRing R] (ι : Type u)
    [Fintype ι] [DecidableEq ι] :
    (matrixSpaceOpenIso R ι).hom ≫ toMatrixSpace R ι = (matrixSpaceOpen R ι).ι := sorry

/-- The open range of the general linear locus is the determinant basic open. -/
@[simp]
theorem toMatrixSpace_opensRange (R : Type u) [CommRing R] (ι : Type u)
    [Fintype ι] [DecidableEq ι] :
    (toMatrixSpace R ι).opensRange = D(determinant R ι) := sorry

/-- The structure morphism from matrix affine space to `Spec(R)`. -/
@[stacks 01KX "matrix-space structure morphism"]
noncomputable abbrev matrixSpaceToBase (R : Type u) [CommRing R] (ι : Type u) :
    matrixSpace R ι ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* polynomialRing R ι))

/-- The structure morphism from the general linear scheme to `Spec(R)`. -/
@[stacks 01KX "general-linear structure morphism"]
noncomputable abbrev toBase (R : Type u) [CommRing R] (ι : Type u)
    [Fintype ι] [DecidableEq ι] : scheme R ι ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (coordinateRing R ι)))

/-- The general linear structure morphism factors through matrix affine space. -/
@[reassoc]
theorem toMatrixSpace_toBase (R : Type u) [CommRing R] (ι : Type u)
    [Fintype ι] [DecidableEq ι] :
    toMatrixSpace R ι ≫ matrixSpaceToBase R ι = toBase R ι := sorry

/-- The general linear scheme bundled with its structure morphism to `Spec(R)`. -/
@[stacks 01KX "general-linear scheme over its base"]
noncomputable abbrev schemeOver (R : Type u) [CommRing R] (ι : Type u)
    [Fintype ι] [DecidableEq ι] : Over (Spec (CommRingCat.of R)) :=
  Scheme.OverSpec.affine
    (CommRingCat.ofHom (algebraMap R (coordinateRing R ι)))

/-- The underlying scheme of `schemeOver R ι` is `scheme R ι`. -/
@[simp]
theorem schemeOver_left (R : Type u) [CommRing R] (ι : Type u)
    [Fintype ι] [DecidableEq ι] :
    (schemeOver R ι).left = scheme R ι := sorry

/-- The structure morphism of `schemeOver R ι` is `toBase R ι`. -/
@[simp]
theorem schemeOver_hom (R : Type u) [CommRing R] (ι : Type u)
    [Fintype ι] [DecidableEq ι] :
    (schemeOver R ι).hom = toBase R ι := sorry

namespace HomOver

namespace Compatible

/-- The coordinate-ring map induced by a matrix over `Γ(T.left, ⊤)` is compatible with the
structure morphism of `T`. -/
theorem homOfMatrix_w {R : Type u} [CommRing R]
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    {T : Over (Spec (CommRingCat.of R))}
    (M : Matrix.GeneralLinearGroup ι Γ(T.left, ⊤)) :
    CommRingCat.ofHom (algebraMap R (coordinateRing R ι)) ≫
        CommRingCat.ofHom
          (CoordinateRing.homOfMatrix ι (Scheme.OverSpec.baseRingHom T).hom M) =
      Scheme.OverSpec.baseRingHom T := sorry

/-- The base-compatible coordinate-ring homomorphism represented by an invertible matrix. -/
@[stacks 01KX "compatible matrix-valued point"]
noncomputable def homOfMatrix {R : Type u} [CommRing R]
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    {T : Over (Spec (CommRingCat.of R))}
    (M : Matrix.GeneralLinearGroup ι Γ(T.left, ⊤)) :
    Scheme.OverSpec.CompatibleRingHom
      (CommRingCat.ofHom (algebraMap R (coordinateRing R ι))) T :=
  Under.homMk
    (CommRingCat.ofHom
      (CoordinateRing.homOfMatrix ι (Scheme.OverSpec.baseRingHom T).hom M))
    (homOfMatrix_w ι M)

/-- Evaluate a base-compatible coordinate-ring homomorphism on the universal matrix. -/
@[stacks 01KX "matrix of a compatible coordinate-ring homomorphism"]
noncomputable def matrixOfHom {R : Type u} [CommRing R]
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    {T : Over (Spec (CommRingCat.of R))}
    (ψ : Scheme.OverSpec.CompatibleRingHom
      (CommRingCat.ofHom (algebraMap R (coordinateRing R ι))) T) :
    Matrix.GeneralLinearGroup ι Γ(T.left, ⊤) :=
  CoordinateRing.matrixOfHom ι ψ.right.hom

/-- Reconstructing a compatible coordinate-ring homomorphism from its matrix is the identity. -/
@[simp]
theorem homOfMatrix_matrixOfHom {R : Type u} [CommRing R]
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    {T : Over (Spec (CommRingCat.of R))}
    (ψ : Scheme.OverSpec.CompatibleRingHom
      (CommRingCat.ofHom (algebraMap R (coordinateRing R ι))) T) :
    homOfMatrix ι (matrixOfHom ι ψ) = ψ := sorry

/-- Evaluating the compatible coordinate-ring homomorphism represented by a matrix recovers that
matrix. -/
@[simp]
theorem matrixOfHom_homOfMatrix {R : Type u} [CommRing R]
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    {T : Over (Spec (CommRingCat.of R))}
    (M : Matrix.GeneralLinearGroup ι Γ(T.left, ⊤)) :
    matrixOfHom ι (homOfMatrix ι M) = M := sorry

/-- Base-compatible coordinate-ring homomorphisms are canonically equivalent to invertible
matrices over global sections. -/
@[stacks 01KX "compatible general linear functor of points"]
noncomputable def equiv {R : Type u} [CommRing R]
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (T : Over (Spec (CommRingCat.of R))) :
    Scheme.OverSpec.CompatibleRingHom
        (CommRingCat.ofHom (algebraMap R (coordinateRing R ι))) T ≃
      Matrix.GeneralLinearGroup ι Γ(T.left, ⊤) where
  toFun := matrixOfHom ι
  invFun := homOfMatrix ι
  left_inv := homOfMatrix_matrixOfHom ι
  right_inv := matrixOfHom_homOfMatrix ι

end Compatible

/-- Morphisms over `Spec(R)` into the general-linear scheme are canonically equivalent to
invertible matrices over global sections. -/
@[stacks 01KX "general linear scheme functor of points"]
noncomputable def equiv {R : Type u} [CommRing R]
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (T : Over (Spec (CommRingCat.of R))) :
    (T ⟶ schemeOver R ι) ≃ Matrix.GeneralLinearGroup ι Γ(T.left, ⊤) :=
  (Scheme.OverSpec.homEquiv
    (CommRingCat.ofHom (algebraMap R (coordinateRing R ι))) T).trans
      (Compatible.equiv ι T)

/-- Evaluate the universal matrix on a morphism over `Spec(R)` into the general linear scheme. -/
@[stacks 01KX "matrix evaluated on an over-morphism"]
noncomputable abbrev matrixOfHom {R : Type u} [CommRing R]
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    {T : Over (Spec (CommRingCat.of R))} (f : T ⟶ schemeOver R ι) :
    Matrix.GeneralLinearGroup ι Γ(T.left, ⊤) :=
  equiv ι T f

/-- The canonical morphism over `Spec(R)` represented by an invertible matrix over global
sections. -/
@[stacks 01KX "matrix-valued point of the general linear scheme"]
noncomputable abbrev ofMatrix {R : Type u} [CommRing R]
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    {T : Over (Spec (CommRingCat.of R))}
    (M : Matrix.GeneralLinearGroup ι Γ(T.left, ⊤)) : T ⟶ schemeOver R ι :=
  (equiv ι T).symm M

/-- Entries of the matrix evaluated at an over-morphism are pullbacks of universal
coordinates. -/
@[simp]
theorem matrixOfHom_apply {R : Type u} [CommRing R]
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    {T : Over (Spec (CommRingCat.of R))} (f : T ⟶ schemeOver R ι) (i j : ι) :
    matrixOfHom ι f i j =
      (Scheme.OverSpec.ringHomOfHom
        (CommRingCat.ofHom (algebraMap R (coordinateRing R ι))) f).right
          (localizedCoordinate R ι i j) := sorry

/-- Reconstructing an over-morphism from its evaluated universal matrix is the identity. -/
@[simp]
theorem ofMatrix_matrixOfHom {R : Type u} [CommRing R]
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    {T : Over (Spec (CommRingCat.of R))} (f : T ⟶ schemeOver R ι) :
    ofMatrix ι (matrixOfHom ι f) = f :=
  (equiv ι T).symm_apply_apply f

/-- Evaluating the over-morphism represented by a matrix recovers that matrix. -/
@[simp]
theorem matrixOfHom_ofMatrix {R : Type u} [CommRing R]
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    {T : Over (Spec (CommRingCat.of R))}
    (M : Matrix.GeneralLinearGroup ι Γ(T.left, ⊤)) :
    matrixOfHom ι (ofMatrix ι M) = M :=
  (equiv ι T).apply_symm_apply M

/-- Evaluation of the universal matrix bijects morphisms over `Spec(R)` into the general linear
scheme with invertible matrices over global sections. -/
@[stacks 01KX "general linear scheme functor of points"]
theorem matrixOfHom_bijective {R : Type u} [CommRing R]
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (T : Over (Spec (CommRingCat.of R))) :
    Function.Bijective (matrixOfHom (T := T) ι) :=
  (equiv ι T).bijective

/-- Every invertible matrix over the global sections of an `R`-scheme has a unique representing
morphism over `Spec(R)` into the general linear scheme. -/
theorem existsUnique {R : Type u} [CommRing R]
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (T : Over (Spec (CommRingCat.of R)))
    (M : Matrix.GeneralLinearGroup ι Γ(T.left, ⊤)) :
    ∃! f : T ⟶ schemeOver R ι, matrixOfHom ι f = M := sorry

/-- Evaluation of the universal matrix is natural under precomposition over `Spec(R)`. -/
theorem matrixOfHom_comp {R : Type u} [CommRing R]
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    {T T' : Over (Spec (CommRingCat.of R))}
    (g : T' ⟶ T) (f : T ⟶ schemeOver R ι) :
    matrixOfHom ι (g ≫ f) =
      Matrix.GeneralLinearGroup.map (Scheme.Γ.map g.left.op).hom (matrixOfHom ι f) := sorry

end HomOver

end AlgebraicGeometry.GeneralLinear
