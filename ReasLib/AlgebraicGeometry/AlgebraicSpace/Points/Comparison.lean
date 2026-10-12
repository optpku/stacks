/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Logic.Equiv.Defs
public import ReasLib.AlgebraicGeometry.Scheme.FieldValuedPoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points

/-!
# Scheme points versus algebraic-space points

A scheme over `S`, viewed as an algebraic space via `ofOver`, has field-valued points
canonically equivalent to the field-valued points of its underlying scheme. Passing to
equivalence classes yields a correspondence between the points of `X` as a scheme and the
points of `X` as an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

namespace FieldValuedPoint

/-- View a field-valued point of the underlying scheme of `X : Over S` as a field-valued point
of the algebraic space `ofOver X`. -/
def ofScheme {X : Over S} (p : Scheme.FieldValuedPoint X.left) :
    FieldValuedPoint (ofOver X) :=
  FieldValuedPoint.of p.K (p.hom ≫ X.hom) (yoneda.map (Over.homMk p.hom))

/-- Recover the underlying scheme morphism of a field-valued point of `ofOver X`. -/
def toScheme {X : Over S} (q : FieldValuedPoint (ofOver X)) :
    Scheme.FieldValuedPoint X.left :=
  @Scheme.FieldValuedPoint.of X.left q.K q.field (yonedaEquiv q.hom).left

end FieldValuedPoint

namespace ofOver

/-- The scheme comparison followed by its inverse recovers the original scheme point. -/
theorem fieldValuedPointEquiv_left_inv (X : Over S)
    (p : Scheme.FieldValuedPoint X.left) :
    FieldValuedPoint.toScheme (FieldValuedPoint.ofScheme p) = p := sorry

/-- The algebraic-space comparison followed by its inverse recovers the original point. -/
theorem fieldValuedPointEquiv_right_inv (X : Over S)
    (q : FieldValuedPoint (ofOver X)) :
    FieldValuedPoint.ofScheme (FieldValuedPoint.toScheme q) = q := sorry

/-- Field-valued points of a scheme over `S` correspond to field-valued points of the
associated algebraic space. -/
def fieldValuedPointEquiv (X : Over S) :
    Scheme.FieldValuedPoint X.left ≃ FieldValuedPoint (ofOver X) where
  toFun := FieldValuedPoint.ofScheme
  invFun := FieldValuedPoint.toScheme
  left_inv := fieldValuedPointEquiv_left_inv X
  right_inv := fieldValuedPointEquiv_right_inv X

/-- The representative equivalence identifies the scheme-side and algebraic-space-side
common-extension relations. -/
theorem fieldValuedPointEquiv_rel (X : Over S)
    (p q : Scheme.FieldValuedPoint X.left) :
    Scheme.FieldValuedPoint.equivalentSetoid X.left p q ↔
      equivalentSetoid (ofOver X)
        (fieldValuedPointEquiv X p) (fieldValuedPointEquiv X q) := sorry

/-- The points of a scheme over `S` are in canonical bijection with the points of the
associated algebraic space. -/
def pointsEquiv (X : Over S) : X.left ≃ Points (ofOver X) :=
  (Scheme.FieldValuedPoint.classesEquiv X.left).symm.trans
    (Quotient.congr (fieldValuedPointEquiv X) (fieldValuedPointEquiv_rel X))

/-- The forward map of `pointsEquiv` sends a scheme point to the class of its residue-field
point, viewed as a field-valued point of `ofOver X`. -/
theorem pointsEquiv_apply (X : Over S) (x : X.left) :
    pointsEquiv X x =
      Points.mk (FieldValuedPoint.ofScheme (Scheme.FieldValuedPoint.residuePoint x)) := sorry

/-- The inverse map of `pointsEquiv` sends the class of a field-valued point to the image of
the corresponding morphism of schemes. -/
theorem pointsEquiv_symm_apply (X : Over S) (p : FieldValuedPoint (ofOver X)) :
    (pointsEquiv X).symm (Points.mk p) = (FieldValuedPoint.toScheme p).image := sorry

/-- The comparison of points is natural in morphisms of schemes over `S`. -/
theorem pointsEquiv_naturality {X Y : Over S} (f : X ⟶ Y) (x : X.left) :
    pointsEquiv Y (f.left x) = Points.map (ofOverMap f) (pointsEquiv X x) := sorry

end ofOver

end AlgebraicGeometry.AlgebraicSpace
