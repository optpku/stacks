module

public import Mathlib.Data.Setoid.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Presentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points

/-!
# Points of a presentation

A presentation `X = U / R` of an algebraic space induces a pair map `|R| → |U| × |U|`
whose image is an equivalence relation on `|U|`. The space of points `|X|` is the
quotient of `|U|` by that relation, equivalently the quotient of `|U|` by the kernel
of the atlas map `|U| → |X|`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Presentation

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The map on points `|R| → |U| × |U|` induced by the two projections of a presentation. -/
def pointsProdMap (P : Presentation X) :
    Points (ofOver P.R.left) → Points (ofOver P.U) × Points (ofOver P.U) :=
  fun r ↦ (Points.map (ofOverMap P.R.t) r, Points.map (ofOverMap P.R.s) r)

/-- The pair map on points of a presentation sends a point of `|R|` to the pair of its
images under the two projections. -/
theorem pointsProdMap_apply (P : Presentation X) (r : Points (ofOver P.R.left)) :
    P.pointsProdMap r =
      (Points.map (ofOverMap P.R.t) r, Points.map (ofOverMap P.R.s) r) :=
  sorry

/-- The map on points `|U| → |X|` induced by the atlas of a presentation. -/
def pointsMap (P : Presentation X) : Points (ofOver P.U) → Points X :=
  Points.map P.atlas

/-- The atlas map on points is `Points.map` of the atlas morphism. -/
theorem pointsMap_apply (P : Presentation X) (u : Points (ofOver P.U)) :
    P.pointsMap u = Points.map P.atlas u :=
  sorry

/-- The image relation of `|R| → |U| × |U|` on the points of `|U|`. -/
def pointsRel (P : Presentation X) : Points (ofOver P.U) → Points (ofOver P.U) → Prop :=
  fun u v ↦ ∃ r, Points.map (ofOverMap P.R.t) r = u ∧ Points.map (ofOverMap P.R.s) r = v

/-- Two points of `|U|` are related by `pointsRel` exactly when they lie in the image of
the pair map `|R| → |U| × |U|`. -/
theorem pointsRel_iff (P : Presentation X) (u v : Points (ofOver P.U)) :
    P.pointsRel u v ↔ ∃ r, P.pointsProdMap r = (u, v) :=
  sorry

/-- The image of `|R| → |U| × |U|` is an equivalence relation on `|U|`. -/
theorem pointsRel_equivalence (P : Presentation X) : Equivalence P.pointsRel :=
  sorry

/-- The image relation of `|R| → |U| × |U|` is the kernel of the atlas map `|U| → |X|`. -/
theorem pointsRel_iff_map_eq (P : Presentation X) (u v : Points (ofOver P.U)) :
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
theorem pointsQuotientLift_mk (P : Presentation X) (u : Points (ofOver P.U)) :
    pointsQuotientLift P (Quotient.mk _ u) = P.pointsMap u :=
  sorry

/-- The kernel lift of the atlas identifies the quotient of `|U|` by that kernel with `|X|`. -/
theorem pointsQuotientLift_bijective (P : Presentation X) :
    Function.Bijective (pointsQuotientLift P) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Presentation
