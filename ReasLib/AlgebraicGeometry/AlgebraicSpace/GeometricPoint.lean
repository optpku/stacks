/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Comparison

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

/-- Explicit field and morphism data for a geometric point of an algebraic space. -/
structure GeometricPointObj {S : Scheme.{u}} (X : AlgebraicSpace S) where
  /-- The source field. -/
  K : Type u
  /-- The field structure on the source. -/
  [field : Field K]
  /-- The structure morphism of the source-field spectrum to the base scheme. -/
  structureHom : Spec (.of K) ⟶ S
  /-- The morphism from the source-field spectrum into the algebraic space. -/
  hom : ofOver (Over.mk structureHom) ⟶ X
  /-- The source field is algebraically closed. -/
  isAlgClosed : IsAlgClosed K

/-- The field-valued point with exactly the stored field and morphisms of a geometric point. -/
def GeometricPointObj.toFieldValuedPoint {S : Scheme.{u}} {X : AlgebraicSpace S}
    (p : GeometricPointObj X) : FieldValuedPoint X :=
  @FieldValuedPoint.of S X p.K p.field p.structureHom p.hom

/-- Geometric points with morphisms induced from their underlying field-valued points. -/
abbrev GeometricPoint {S : Scheme.{u}} (X : AlgebraicSpace S) :=
  InducedCategory (FieldValuedPoint X) (GeometricPointObj.toFieldValuedPoint (X := X))

namespace GeometricPoint

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The underlying field-valued point, retaining the source field and both morphisms. -/
def toFieldValuedPoint (p : GeometricPoint X) : FieldValuedPoint X :=
  GeometricPointObj.toFieldValuedPoint p

/-- The source-field carrier of a geometric point. -/
abbrev K (p : GeometricPoint X) : Type u := p.toFieldValuedPoint.K

/-- The field structure stored in a geometric point. -/
abbrev field (p : GeometricPoint X) : Field p.K := p.toFieldValuedPoint.field

/-- The structure morphism from the source-field spectrum to the base scheme. -/
abbrev structureHom (p : GeometricPoint X) : Spec (.of p.K) ⟶ S :=
  GeometricPointObj.structureHom p

/-- The morphism from the source-field spectrum into the algebraic space. -/
abbrev hom (p : GeometricPoint X) : ofOver (Over.mk p.structureHom) ⟶ X :=
  GeometricPointObj.hom p

/-- The stored algebraic closedness of the source field. -/
abbrev isAlgClosed (p : GeometricPoint X) : IsAlgClosed p.K :=
  GeometricPointObj.isAlgClosed p

/-- The source-field spectrum as a scheme over the base scheme. -/
abbrev overObj (p : GeometricPoint X) : Over S := p.toFieldValuedPoint.overObj

/-- A field-valued point with algebraically closed source field determines a geometric point. -/
def ofFieldValuedPoint (p : FieldValuedPoint X) (h : IsAlgClosed p.K) : GeometricPoint X :=
  { K := p.K
    field := p.field
    structureHom := p.structureHom
    hom := p.hom
    isAlgClosed := h }

/-- The induced forgetful functor from geometric points to field-valued points. -/
def toFieldValuedPointFunctor (X : AlgebraicSpace S) : GeometricPoint X ⥤ FieldValuedPoint X :=
  inducedFunctor GeometricPoint.toFieldValuedPoint

/-- The forgetful functor from geometric points to field-valued points is fully faithful. -/
def toFieldValuedPointFullyFaithful (X : AlgebraicSpace S) :
    (toFieldValuedPointFunctor X).FullyFaithful :=
  fullyFaithfulInducedFunctor GeometricPoint.toFieldValuedPoint

/-- Construct a geometric point from an algebraically closed field, a structure morphism to
`S`, and a morphism into `X`. -/
def of (K : Type u) [Field K] [IsAlgClosed K] (structureHom : Spec (.of K) ⟶ S)
    (hom : ofOver (Over.mk structureHom) ⟶ X) : GeometricPoint X where
  K := K
  field := inferInstance
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
def map {Y : AlgebraicSpace S} (xbar : GeometricPoint X) (f : X ⟶ Y) : GeometricPoint Y :=
  ofFieldValuedPoint (xbar.toFieldValuedPoint.map f) (by
    change IsAlgClosed xbar.K
    exact xbar.isAlgClosed)

/-- The image of a postcomposed geometric point is the image of the original point under the
induced map on `|X|`. -/
@[simp]
theorem map_image {Y : AlgebraicSpace S} (xbar : GeometricPoint X) (f : X ⟶ Y) :
    (xbar.map f).image = Points.map f xbar.image := sorry

/-- View a geometric point of the underlying scheme of `U : Over S` as a geometric point of the
algebraic space `ofOver U`. -/
def ofScheme {U : Over S} (p : Scheme.GeometricPoint U.left) : GeometricPoint (ofOver U) :=
  ofFieldValuedPoint (FieldValuedPoint.ofScheme p.toFieldValuedPoint) p.isAlgClosed

/-- Recover the underlying scheme geometric point of a geometric point of `ofOver U`. -/
def toScheme {U : Over S} (p : GeometricPoint (ofOver U)) : Scheme.GeometricPoint U.left where
  toFieldValuedPoint := FieldValuedPoint.toScheme p.toFieldValuedPoint
  isAlgClosed := by
    change IsAlgClosed p.K
    exact p.isAlgClosed

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
