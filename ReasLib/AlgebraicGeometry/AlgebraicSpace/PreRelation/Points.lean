module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Points of a pre-relation of algebraic spaces

A pre-relation `j : R ⟶ U ×_B U` induces an image relation on the points of `U`.
For a pre-equivalence relation, this image relation is an equivalence relation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

variable {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}

/-- The image relation of `|R| → |U| × |U|` on the points of `|U|`. -/
def pointsRel (P : PreRelation U) : Points U.left → Points U.left → Prop :=
  fun x y ↦ ∃ r : Points P.left.left,
    Points.map P.t.left r = x ∧ Points.map P.s.left r = y

/-- Two points of `|U|` are related exactly when they lie in the image of the pair map
`|R| → |U| × |U|` given by `t` and `s`. -/
theorem pointsRel_iff (P : PreRelation U) (x y : Points U.left) :
    pointsRel P x y ↔
      ∃ r : Points P.left.left,
        Points.map P.t.left r = x ∧ Points.map P.s.left r = y :=
  Iff.rfl

/-- A pre-equivalence relation induces an equivalence relation on the underlying point set. -/
theorem pointsRel_equivalence (P : PreRelation U) (hP : P.IsPreEquivalence) :
    Equivalence (pointsRel P) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.PreRelation
