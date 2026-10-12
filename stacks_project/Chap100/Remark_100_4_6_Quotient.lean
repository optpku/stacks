/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.Setoid.Basic
public import stacks_project.Chap94.Lemma_94_16_1_QuotientMap
public import stacks_project.Chap94.Definition_94_12_1_MorphismProperty
public import stacks_project.Chap100.Lemma_100_7_4_Points

/-!
# Points of a kernel-pair groupoid

A space-representable 1-morphism `f : U ⟶ X` into an algebraic stack has a
kernel-pair groupoid `(U, R, s, t, c)`. The induced pair map `|R| → |U| × |U|`
has image an equivalence relation on `|U|` whenever `f` is surjective in the
sense of Section 100.3, and then `|X|` is the quotient of `|U|` by that
relation. The canonical morphism `fCan : [U / R] ⟶ X` is used only as a
comparison; `[U / R]` is not assumed to be an algebraic stack, and `fCan` is not
assumed to be an isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X U : GroupoidsOver S} (f : U ⟶ X) [AlgebraicStack X]
  (hU : IsRepresentableByAlgebraicSpace U)

/-- The map on points `|R| → |U| × |U|` induced by the target and source maps of the
kernel-pair groupoid of `f`. -/
def pointsProdMap :
    AlgebraicSpace.Points (groupoid f hU).R.left →
      AlgebraicSpace.Points (groupoid f hU).U.left ×
        AlgebraicSpace.Points (groupoid f hU).U.left :=
  fun r ↦
    (AlgebraicSpace.Points.map (groupoid f hU).t.left r,
      AlgebraicSpace.Points.map (groupoid f hU).s.left r)

/-- The pair map on points sends a point of `|R|` to the pair of its images under
target and source. -/
theorem pointsProdMap_apply (r : AlgebraicSpace.Points (groupoid f hU).R.left) :
    pointsProdMap f hU r =
      (AlgebraicSpace.Points.map (groupoid f hU).t.left r,
        AlgebraicSpace.Points.map (groupoid f hU).s.left r) :=
  sorry

/-- The map on points `|U| → |X|` induced by `f` after presenting the object space of
the kernel-pair groupoid. This is not the map of points of the quotient stack
`[U / R]`. -/
def pointsMap :
    AlgebraicSpace.Points (groupoid f hU).U.left → Points X :=
  Points.mapSpace (fFromObjectSpace f hU)

/-- The atlas map on points is `Points.mapSpace` of `fFromObjectSpace`. -/
theorem pointsMap_apply (u : AlgebraicSpace.Points (groupoid f hU).U.left) :
    pointsMap f hU u = Points.mapSpace (fFromObjectSpace f hU) u :=
  sorry

/-- The atlas map on points agrees with `Points.mapSpace` of the atlas composite of
`fCan`. This does not assume that `fCan` is an isomorphism. -/
theorem pointsMap_eq_fCan_atlas :
    pointsMap f hU = Points.mapSpace (fCan_atlas f hU) :=
  sorry

/-- The image relation of `|R| → |U| × |U|` on the points of `|U|`. -/
def pointsRel :
    AlgebraicSpace.Points (groupoid f hU).U.left →
      AlgebraicSpace.Points (groupoid f hU).U.left → Prop :=
  fun u v ↦ ∃ r : AlgebraicSpace.Points (groupoid f hU).R.left,
    AlgebraicSpace.Points.map (groupoid f hU).t.left r = u ∧
      AlgebraicSpace.Points.map (groupoid f hU).s.left r = v

/-- Two points of `|U|` are related by `pointsRel` exactly when they lie in the image
of the pair map `|R| → |U| × |U|`. -/
theorem pointsRel_iff (u v : AlgebraicSpace.Points (groupoid f hU).U.left) :
    pointsRel f hU u v ↔ ∃ r, pointsProdMap f hU r = (u, v) :=
  sorry

/-- The image of `|R| → |U| × |U|` is an equivalence relation on `|U|`. -/
theorem pointsRel_equivalence [Groupoids.Hom.Surjective f] :
    Equivalence (pointsRel f hU) :=
  sorry

/-- The image relation of `|R| → |U| × |U|` is the kernel of the atlas map `|U| → |X|`. -/
theorem pointsRel_iff_map_eq (u v : AlgebraicSpace.Points (groupoid f hU).U.left) :
    pointsRel f hU u v ↔ pointsMap f hU u = pointsMap f hU v :=
  sorry

/-- A Section 100.3 surjective space morphism is surjective on points. -/
theorem pointsMap_surjective [Groupoids.Hom.Surjective f] :
    Function.Surjective (pointsMap f hU) :=
  sorry

/-- The space of points `|X|` is the quotient of `|U|` by the image of `|R| → |U| × |U|`. -/
theorem isPointsQuotient [Groupoids.Hom.Surjective f] :
    Function.Surjective (pointsMap f hU) ∧
      ∀ u v, pointsRel f hU u v ↔ pointsMap f hU u = pointsMap f hU v :=
  sorry

/-- The canonical map from the quotient of `|U|` by the kernel of the atlas to `|X|`. -/
def pointsQuotientLift :
    Quotient (Setoid.ker (pointsMap f hU)) → Points X :=
  Setoid.kerLift (pointsMap f hU)

/-- The kernel lift of the atlas sends the class of a point of `|U|` to its image in `|X|`. -/
theorem pointsQuotientLift_mk (u : AlgebraicSpace.Points (groupoid f hU).U.left) :
    pointsQuotientLift f hU (Quotient.mk _ u) = pointsMap f hU u :=
  sorry

/-- The kernel lift of the atlas identifies the quotient of `|U|` by that kernel with `|X|`. -/
theorem pointsQuotientLift_bijective [Groupoids.Hom.Surjective f] :
    Function.Bijective (pointsQuotientLift f hU) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
