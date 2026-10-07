module

public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap78.Lemma_78_4_2_PreRelation

/-!
# Points of a pre-relation of algebraic spaces

A pre-relation `j : R ⟶ U ×_B U` of algebraic spaces over `B` induces a relation on the
set of points `|U|`. If `j` is a pre-equivalence relation, that relation is an equivalence
relation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace PreRelation

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
  sorry

/-- If `j` is a pre-equivalence relation, then the induced relation on `|U|` is an
equivalence relation. -/
theorem pointsRel_equivalence (P : PreRelation U) (hP : P.IsPreEquivalence) :
    Equivalence (pointsRel P) :=
  sorry

end PreRelation

end AlgebraicGeometry.AlgebraicSpace
