/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.RingTheory.TensorProduct.Basic
public import ReasLib.AlgebraicGeometry.GeneralLinear.Scheme

/-!
# The general linear group scheme

This module equips the determinant-localized general linear scheme with its canonical group
object structure, records the matrix-multiplication comultiplication on its coordinate ring, and
constructs its base changes.
-/

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Limits
open scoped AlgebraicGeometry CategoryTheory.MonObj TensorProduct CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.GeneralLinear

/-- The group of invertible matrices over the global sections of an object over `Spec(R)`. -/
def functorOfPointsObj {R : Type u} [CommRing R] (I : Type u)
    [Fintype I] [DecidableEq I] (T : (Over (Spec (CommRingCat.of R)))ᵒᵖ) : GrpCat.{u} :=
  GrpCat.of (Matrix.GeneralLinearGroup I Γ((unop T).left, ⊤))

/-- The point-group map induced by pullback of global sections. -/
def functorOfPointsMap {R : Type u} [CommRing R] (I : Type u)
    [Fintype I] [DecidableEq I] {T T' : (Over (Spec (CommRingCat.of R)))ᵒᵖ}
    (f : T ⟶ T') : functorOfPointsObj I T ⟶ functorOfPointsObj I T' :=
  GrpCat.ofHom (Matrix.GeneralLinearGroup.map (Scheme.Γ.map f.unop.left.op).hom)

/-- Pullback of matrix-valued points preserves identity morphisms. -/
theorem functorOfPointsMap_id {R : Type u} [CommRing R] (I : Type u)
    [Fintype I] [DecidableEq I] (T : (Over (Spec (CommRingCat.of R)))ᵒᵖ) :
    functorOfPointsMap I (𝟙 T) = 𝟙 (functorOfPointsObj I T) := sorry

/-- Pullback of matrix-valued points preserves composition. -/
theorem functorOfPointsMap_comp {R : Type u} [CommRing R] (I : Type u)
    [Fintype I] [DecidableEq I] {T T' T'' : (Over (Spec (CommRingCat.of R)))ᵒᵖ}
    (f : T ⟶ T') (g : T' ⟶ T'') :
    functorOfPointsMap I (f ≫ g) = functorOfPointsMap I f ≫ functorOfPointsMap I g := sorry

/-- The group-valued functor of invertible matrices over global sections. -/
def functorOfPoints (R : Type u) [CommRing R] (I : Type u)
    [Fintype I] [DecidableEq I] :
    (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ GrpCat.{u} where
  obj := functorOfPointsObj I
  map := functorOfPointsMap I
  map_id := functorOfPointsMap_id I
  map_comp := functorOfPointsMap_comp I

/-- The value of the matrix-valued functor on an object is its general linear group. -/
theorem functorOfPoints_obj (R : Type u) [CommRing R] (I : Type u)
    [Fintype I] [DecidableEq I] (T : (Over (Spec (CommRingCat.of R)))ᵒᵖ) :
    (functorOfPoints R I).obj T =
      GrpCat.of (Matrix.GeneralLinearGroup I Γ((unop T).left, ⊤)) := sorry

/-- The matrix-valued functor acts by applying the induced map on global sections entrywise. -/
theorem functorOfPoints_map_apply (R : Type u) [CommRing R] (I : Type u)
    [Fintype I] [DecidableEq I] {T T' : (Over (Spec (CommRingCat.of R)))ᵒᵖ}
    (f : T ⟶ T') (M : Matrix.GeneralLinearGroup I Γ((unop T).left, ⊤)) :
    (functorOfPoints R I).map f M =
      Matrix.GeneralLinearGroup.map (Scheme.Γ.map f.unop.left.op).hom M := sorry

/-- The universal-matrix equivalence is natural under precomposition. -/
theorem functorOfPoints_homEquiv_comp {R : Type u} [CommRing R] (I : Type u)
    [Fintype I] [DecidableEq I]
    {T T' : Over (Spec (CommRingCat.of R))} (f : T ⟶ T') (g : T' ⟶ schemeOver R I) :
    HomOver.equiv I T (f ≫ g) =
      (functorOfPoints R I ⋙ forget GrpCat).map f.op (HomOver.equiv I T' g) := sorry

/-- The general linear scheme represents the underlying set-valued matrix functor. -/
def functorOfPointsRepresentableBy (R : Type u) [CommRing R] (I : Type u)
    [Fintype I] [DecidableEq I] :
    (functorOfPoints R I ⋙ forget GrpCat).RepresentableBy (schemeOver R I) where
  homEquiv := HomOver.equiv I _
  homEquiv_comp := functorOfPoints_homEquiv_comp I

/-- The representing equivalence evaluates morphisms on the universal invertible matrix. -/
theorem functorOfPointsRepresentableBy_homEquiv (R : Type u) [CommRing R] (I : Type u)
    [Fintype I] [DecidableEq I] (T : Over (Spec (CommRingCat.of R))) :
    (functorOfPointsRepresentableBy R I).homEquiv = HomOver.equiv I T := sorry

/-- The canonical group-object structure on the general linear scheme over `Spec(R)`. -/
noncomputable instance instGrpObjSchemeOver (R : Type u) [CommRing R] (I : Type u)
    [Fintype I] [DecidableEq I] : GrpObj (schemeOver R I) :=
  GrpObj.ofRepresentableBy (schemeOver R I) (functorOfPoints R I)
    (functorOfPointsRepresentableBy R I)

/-- The general linear group scheme over `Spec(R)`. -/
def groupScheme (R : Type u) [CommRing R] (I : Type u)
    [Fintype I] [DecidableEq I] : Grp (Over (Spec (CommRingCat.of R))) :=
  { X := schemeOver R I }

/-- The underlying object of the general linear group scheme is `schemeOver R I`. -/
theorem groupScheme_X (R : Type u) [CommRing R] (I : Type u)
    [Fintype I] [DecidableEq I] : (groupScheme R I).X = schemeOver R I := sorry

/-- The underlying scheme of the general linear group scheme is the determinant-localized
spectrum. -/
theorem groupScheme_left (R : Type u) [CommRing R] (I : Type u)
    [Fintype I] [DecidableEq I] :
    (groupScheme R I).X.left = Spec (CommRingCat.of (coordinateRing R I)) := sorry

namespace CoordinateRing

/-- The coordinate-ring comultiplication induced by multiplication of the two universal
invertible matrices. -/
def comul (R : Type u) [CommRing R] (I : Type u)
    [Fintype I] [DecidableEq I] :
    coordinateRing R I →ₐ[R] coordinateRing R I ⊗[R] coordinateRing R I :=
  algHomOfMatrix I
    (Matrix.GeneralLinearGroup.map
        (Algebra.TensorProduct.includeLeft :
          coordinateRing R I →ₐ[R] coordinateRing R I ⊗[R] coordinateRing R I).toRingHom
        (universalMatrix R I) *
      Matrix.GeneralLinearGroup.map
        (Algebra.TensorProduct.includeRight :
          coordinateRing R I →ₐ[R] coordinateRing R I ⊗[R] coordinateRing R I).toRingHom
        (universalMatrix R I))

/-- On matrix coordinates, comultiplication is the formula
`xᵢⱼ ↦ ∑ k, xᵢₖ ⊗ xₖⱼ`. -/
theorem comul_localizedCoordinate (R : Type u) [CommRing R] (I : Type u)
    [Fintype I] [DecidableEq I] (i j : I) :
    comul R I (localizedCoordinate R I i j) =
      ∑ k, (Algebra.TensorProduct.includeLeft :
          coordinateRing R I →ₐ[R] coordinateRing R I ⊗[R] coordinateRing R I)
          (localizedCoordinate R I i k) *
        (Algebra.TensorProduct.includeRight :
          coordinateRing R I →ₐ[R] coordinateRing R I ⊗[R] coordinateRing R I)
          (localizedCoordinate R I k j) := sorry

end CoordinateRing

namespace HomOver

/-- Evaluation of the universal matrix respects multiplication of points. -/
theorem matrixOfHom_mul {R : Type u} [CommRing R] (I : Type u)
    [Fintype I] [DecidableEq I] {T : Over (Spec (CommRingCat.of R))}
    (f g : T ⟶ schemeOver R I) :
    matrixOfHom I (f * g) = matrixOfHom I f * matrixOfHom I g := sorry

/-- Entrywise, multiplication of points is ordinary matrix multiplication. -/
theorem matrixOfHom_mul_apply {R : Type u} [CommRing R] (I : Type u)
    [Fintype I] [DecidableEq I] {T : Over (Spec (CommRingCat.of R))}
    (f g : T ⟶ schemeOver R I) (i j : I) :
    matrixOfHom I (f * g) i j =
      ∑ k, matrixOfHom I f i k * matrixOfHom I g k j := sorry

/-- Morphisms into the general linear scheme are multiplicatively equivalent to invertible
matrices over global sections. -/
def mulEquiv {R : Type u} [CommRing R] (I : Type u)
    [Fintype I] [DecidableEq I] (T : Over (Spec (CommRingCat.of R))) :
    (T ⟶ schemeOver R I) ≃* Matrix.GeneralLinearGroup I Γ(T.left, ⊤) where
  toEquiv := equiv I T
  map_mul' := matrixOfHom_mul I

/-- The forward map of `mulEquiv` evaluates the universal invertible matrix. -/
theorem mulEquiv_apply {R : Type u} [CommRing R] (I : Type u)
    [Fintype I] [DecidableEq I] (T : Over (Spec (CommRingCat.of R)))
    (f : T ⟶ schemeOver R I) : mulEquiv I T f = matrixOfHom I f := sorry

/-- The inverse of `mulEquiv` is the morphism classified by an invertible matrix. -/
theorem mulEquiv_symm_apply {R : Type u} [CommRing R] (I : Type u)
    [Fintype I] [DecidableEq I] (T : Over (Spec (CommRingCat.of R)))
    (M : Matrix.GeneralLinearGroup I Γ(T.left, ⊤)) :
    (mulEquiv I T).symm M = ofMatrix I M := sorry

end HomOver

/-- The scheme morphism dual to comultiplication on the coordinate ring of the general linear
scheme. -/
noncomputable def specMapComul (R : Type u) [CommRing R] (I : Type u)
    [Fintype I] [DecidableEq I] :
    (schemeOver R I ⊗ schemeOver R I).left ⟶ (schemeOver R I).left :=
  (pullbackSpecIso R (coordinateRing R I) (coordinateRing R I)).hom ≫
    Spec.map (CommRingCat.ofHom (CoordinateRing.comul R I).toRingHom)

/-- Categorical multiplication on the general linear group scheme is dual to the displayed
coordinate-ring comultiplication. -/
theorem mul_eq_specMap_comul (R : Type u) [CommRing R] (I : Type u)
    [Fintype I] [DecidableEq I] :
    μ[schemeOver R I].left = specMapComul R I := sorry

/-- Base change of the general linear group scheme along an explicit morphism. -/
def baseChange {R : Type u} [CommRing R] {S : Scheme.{u}}
    (f : S ⟶ Spec (CommRingCat.of R)) (I : Type u) [Fintype I] [DecidableEq I] :
    Grp (Over S) :=
  (Over.pullback f).mapGrp.obj (groupScheme R I)

/-- The underlying object of `baseChange f I` is the canonical pullback of `schemeOver R I`. -/
theorem baseChange_X {R : Type u} [CommRing R] {S : Scheme.{u}}
    (f : S ⟶ Spec (CommRingCat.of R)) (I : Type u) [Fintype I] [DecidableEq I] :
    (baseChange f I).X = (Over.pullback f).obj (schemeOver R I) := sorry

namespace BaseChange

/-- The pullback adjunction identifies points after base change with points over `Spec(R)`. -/
def pullbackHomEquiv {R : Type u} [CommRing R] {S : Scheme.{u}}
    (f : S ⟶ Spec (CommRingCat.of R)) (I : Type u) [Fintype I] [DecidableEq I]
    (T : Over S) :
    (T ⟶ (baseChange f I).X) ≃
      ((Over.map f).obj T ⟶ (groupScheme R I).X) :=
  (Over.mapPullbackAdj f).homEquiv T (groupScheme R I).X |>.symm

/-- The pullback-adjunction equivalence respects multiplication of points. -/
theorem pullbackHomEquiv_map_mul {R : Type u} [CommRing R] {S : Scheme.{u}}
    (f : S ⟶ Spec (CommRingCat.of R)) (I : Type u) [Fintype I] [DecidableEq I]
    (T : Over S) (g h : T ⟶ (baseChange f I).X) :
    pullbackHomEquiv f I T (g * h) =
      pullbackHomEquiv f I T g * pullbackHomEquiv f I T h := sorry

/-- The multiplicative point equivalence supplied by the pullback adjunction. -/
def pullbackHomMulEquiv {R : Type u} [CommRing R] {S : Scheme.{u}}
    (f : S ⟶ Spec (CommRingCat.of R)) (I : Type u) [Fintype I] [DecidableEq I]
    (T : Over S) :
    (T ⟶ (baseChange f I).X) ≃*
      ((Over.map f).obj T ⟶ (groupScheme R I).X) where
  toEquiv := pullbackHomEquiv f I T
  map_mul' := pullbackHomEquiv_map_mul f I T

/-- Points of a base-changed general linear group scheme are invertible matrices over global
sections. -/
def homMulEquiv {R : Type u} [CommRing R] {S : Scheme.{u}}
    (f : S ⟶ Spec (CommRingCat.of R)) (I : Type u) [Fintype I] [DecidableEq I]
    (T : Over S) :
    (T ⟶ (baseChange f I).X) ≃* Matrix.GeneralLinearGroup I Γ(T.left, ⊤) :=
  (pullbackHomMulEquiv f I T).trans (HomOver.mulEquiv I ((Over.map f).obj T))

/-- The base-changed points equivalence first projects along the pullback and then evaluates the
universal matrix. -/
theorem homMulEquiv_apply {R : Type u} [CommRing R] {S : Scheme.{u}}
    (f : S ⟶ Spec (CommRingCat.of R)) (I : Type u) [Fintype I] [DecidableEq I]
    (T : Over S) (g : T ⟶ (baseChange f I).X) :
    homMulEquiv f I T g =
      HomOver.mulEquiv I ((Over.map f).obj T) (pullbackHomEquiv f I T g) := sorry

/-- The base-changed matrix-valued point is natural under precomposition over the base. -/
theorem homMulEquiv_naturality {R : Type u} [CommRing R] {S : Scheme.{u}}
    (f : S ⟶ Spec (CommRingCat.of R)) (I : Type u) [Fintype I] [DecidableEq I]
    {T T' : Over S} (g : T' ⟶ T) (h : T ⟶ (baseChange f I).X) :
    homMulEquiv f I T' (g ≫ h) =
      Matrix.GeneralLinearGroup.map (Scheme.Γ.map g.left.op).hom (homMulEquiv f I T h) := sorry

end BaseChange

end AlgebraicGeometry.GeneralLinear
