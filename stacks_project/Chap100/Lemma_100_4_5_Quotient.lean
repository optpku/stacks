module

public import Mathlib.Data.Setoid.Basic
public import stacks_project.Chap94.Definition_94_16_5_Presentation
public import stacks_project.Chap100.Lemma_100_7_4_Points

/-!
# Points of a presentation of an algebraic stack

A presentation `X = [U / R]` of an algebraic stack induces a pair map
`|R| → |U| × |U|` whose image is an equivalence relation on `|U|`. The space of
points `|X|` is the quotient of `|U|` by that relation, equivalently the quotient
of `|U|` by the kernel of the atlas map `|U| → |X|`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Presentation

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]

/-- The map on points `|R| → |U| × |U|` induced by the target and source maps of a
presentation. -/
def pointsProdMap (P : Presentation X) :
    AlgebraicSpace.Points P.groupoid.R.left →
      AlgebraicSpace.Points P.groupoid.U.left × AlgebraicSpace.Points P.groupoid.U.left :=
  fun r ↦ (AlgebraicSpace.Points.map P.groupoid.t.left r,
    AlgebraicSpace.Points.map P.groupoid.s.left r)

/-- The pair map on points of a presentation sends a point of `|R|` to the pair of its
images under target and source. -/
theorem pointsProdMap_apply (P : Presentation X)
    (r : AlgebraicSpace.Points P.groupoid.R.left) :
    P.pointsProdMap r =
      (AlgebraicSpace.Points.map P.groupoid.t.left r,
        AlgebraicSpace.Points.map P.groupoid.s.left r) :=
  sorry

/-- The map on points `|U| → |X|` induced by the atlas of a presentation. -/
def pointsMap (P : Presentation X) :
    AlgebraicSpace.Points P.groupoid.U.left → Points X :=
  Points.mapSpace (P.groupoid.atlas ≫ P.hom)

/-- The atlas map on points is `Points.mapSpace` of the composite atlas followed by the
presentation equivalence. -/
theorem pointsMap_apply (P : Presentation X)
    (u : AlgebraicSpace.Points P.groupoid.U.left) :
    P.pointsMap u = Points.mapSpace (P.groupoid.atlas ≫ P.hom) u :=
  sorry

/-- The image relation of `|R| → |U| × |U|` on the points of `|U|`. -/
def pointsRel (P : Presentation X) :
    AlgebraicSpace.Points P.groupoid.U.left → AlgebraicSpace.Points P.groupoid.U.left → Prop :=
  fun u v ↦ ∃ r : AlgebraicSpace.Points P.groupoid.R.left,
    AlgebraicSpace.Points.map P.groupoid.t.left r = u ∧
      AlgebraicSpace.Points.map P.groupoid.s.left r = v

/-- Two points of `|U|` are related by `pointsRel` exactly when they lie in the image of
the pair map `|R| → |U| × |U|`. -/
theorem pointsRel_iff (P : Presentation X)
    (u v : AlgebraicSpace.Points P.groupoid.U.left) :
    P.pointsRel u v ↔ ∃ r, P.pointsProdMap r = (u, v) :=
  sorry

/-- The image of `|R| → |U| × |U|` is an equivalence relation on `|U|`. -/
theorem pointsRel_equivalence (P : Presentation X) : Equivalence P.pointsRel :=
  sorry

/-- The image relation of `|R| → |U| × |U|` is the kernel of the atlas map `|U| → |X|`. -/
theorem pointsRel_iff_map_eq (P : Presentation X)
    (u v : AlgebraicSpace.Points P.groupoid.U.left) :
    P.pointsRel u v ↔ P.pointsMap u = P.pointsMap v :=
  sorry

/-- The atlas of a presentation is surjective on points. -/
theorem pointsMap_surjective (P : Presentation X) : Function.Surjective P.pointsMap :=
  sorry

/-- The space of points `|X|` is the quotient of `|U|` by the image of `|R| → |U| × |U|`. -/
theorem isPointsQuotient (P : Presentation X) :
    Function.Surjective P.pointsMap ∧
      ∀ u v, P.pointsRel u v ↔ P.pointsMap u = P.pointsMap v :=
  sorry

/-- The canonical map from the quotient of `|U|` by the kernel of the atlas to `|X|`. -/
def pointsQuotientLift (P : Presentation X) :
    Quotient (Setoid.ker P.pointsMap) → Points X :=
  Setoid.kerLift P.pointsMap

/-- The kernel lift of the atlas sends the class of a point of `|U|` to its image in `|X|`. -/
theorem pointsQuotientLift_mk (P : Presentation X)
    (u : AlgebraicSpace.Points P.groupoid.U.left) :
    pointsQuotientLift P (Quotient.mk _ u) = P.pointsMap u :=
  sorry

/-- The kernel lift of the atlas identifies the quotient of `|U|` by that kernel with `|X|`. -/
theorem pointsQuotientLift_bijective (P : Presentation X) :
    Function.Bijective (pointsQuotientLift P) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Presentation
