module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import stacks_project.Chap59.Definition_59_29_1_GeometricPoint
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_4_2_Comparison

/-!
# Geometric points of an algebraic space

A geometric point of an algebraic space `X` over a scheme `S` is a morphism
`Spec(k) ⟶ X` over `S` from the spectrum of an algebraically closed field. Its image
in `|X|` is the class of the underlying field-valued point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A geometric point of an algebraic space `X` over a scheme `S` is a morphism
`Spec(k) ⟶ X` over `S` whose source field is algebraically closed. -/
structure GeometricPoint {S : Scheme.{u}} (X : AlgebraicSpace S) extends FieldValuedPoint X where
  /-- The source field of a geometric point is algebraically closed. -/
  isAlgClosed : IsAlgClosed toFieldValuedPoint.K

namespace GeometricPoint

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Construct a geometric point from an algebraically closed field, a structure morphism to
`S`, and a morphism into `X`. -/
def of (K : Type u) [Field K] [IsAlgClosed K] (structureHom : Spec (.of K) ⟶ S)
    (hom : ofOver (Over.mk structureHom) ⟶ X) : GeometricPoint X where
  K := K
  structureHom := structureHom
  hom := hom
  isAlgClosed := inferInstance

/-- The source field of `GeometricPoint.of` is the supplied field. -/
@[simp]
theorem of_K (K : Type u) [Field K] [IsAlgClosed K] (structureHom : Spec (.of K) ⟶ S)
    (hom : ofOver (Over.mk structureHom) ⟶ X) : (of K structureHom hom).K = K := sorry

/-- The structure morphism of `GeometricPoint.of` is the given morphism to `S`. -/
@[simp]
theorem of_structureHom (K : Type u) [Field K] [IsAlgClosed K]
    (structureHom : Spec (.of K) ⟶ S) (hom : ofOver (Over.mk structureHom) ⟶ X) :
    (of K structureHom hom).structureHom = structureHom := sorry

/-- The morphism into `X` of `GeometricPoint.of` is the given morphism. -/
@[simp]
theorem of_hom (K : Type u) [Field K] [IsAlgClosed K] (structureHom : Spec (.of K) ⟶ S)
    (hom : ofOver (Over.mk structureHom) ⟶ X) :
    (of K structureHom hom).hom = hom := sorry

/-- The image point in `|X|` of a geometric point, as the class of the underlying field-valued
point. -/
def image (xbar : GeometricPoint X) : Points X :=
  Points.mk xbar.toFieldValuedPoint

/-- The image of a geometric point is the class of its underlying field-valued point. -/
@[simp]
theorem image_eq (xbar : GeometricPoint X) :
    xbar.image = Points.mk xbar.toFieldValuedPoint := sorry

/-- A geometric point `xbar` lies over a point `x` of `X` if `x` is the image of `xbar`. -/
def liesOver (xbar : GeometricPoint X) (x : Points X) : Prop :=
  xbar.image = x

/-- Lying over a point is equality of that point with the image of the geometric point. -/
theorem liesOver_iff (xbar : GeometricPoint X) (x : Points X) :
    xbar.liesOver x ↔ xbar.image = x := sorry

/-- Postcompose a geometric point with a morphism of algebraic spaces over `S`. -/
def map {Y : AlgebraicSpace S} (xbar : GeometricPoint X) (f : X ⟶ Y) : GeometricPoint Y where
  toFieldValuedPoint := xbar.toFieldValuedPoint.map f
  isAlgClosed := xbar.isAlgClosed

/-- The image of a postcomposed geometric point is the image of the original point under the
induced map on `|X|`. -/
@[simp]
theorem map_image {Y : AlgebraicSpace S} (xbar : GeometricPoint X) (f : X ⟶ Y) :
    (xbar.map f).image = Points.map f xbar.image := sorry

/-- View a geometric point of the underlying scheme of `U : Over S` as a geometric point of the
algebraic space `ofOver U`. -/
def ofScheme {U : Over S} (p : Scheme.GeometricPoint U.left) : GeometricPoint (ofOver U) where
  toFieldValuedPoint := FieldValuedPoint.ofScheme p.toFieldValuedPoint
  isAlgClosed := p.isAlgClosed

/-- Recover the underlying scheme geometric point of a geometric point of `ofOver U`. -/
def toScheme {U : Over S} (p : GeometricPoint (ofOver U)) : Scheme.GeometricPoint U.left where
  toFieldValuedPoint := FieldValuedPoint.toScheme p.toFieldValuedPoint
  isAlgClosed := p.isAlgClosed

/-- The image of `ofScheme p` is the algebraic-space point corresponding to the scheme-theoretic
image of `p`. -/
theorem ofScheme_image {U : Over S} (p : Scheme.GeometricPoint U.left) :
    (ofScheme p).image = ofOver.pointsEquiv U p.image := sorry

/-- The image of `toScheme p` is the scheme point corresponding to the algebraic-space image of
`p`. -/
theorem toScheme_image {U : Over S} (p : GeometricPoint (ofOver U)) :
    (toScheme p).image = (ofOver.pointsEquiv U).symm p.image := sorry

end GeometricPoint

end AlgebraicGeometry.AlgebraicSpace
