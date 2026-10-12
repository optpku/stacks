/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import stacks_project.Chap106.Lemma_106_11_2_DvrUniqueness
public import stacks_project.Chap106.Lemma_106_11_3_FactorsThrough

/-!
# DVR uniqueness along a morphism of algebraic stacks

A morphism of algebraic stacks satisfies uniqueness in the valuative criterion
along a second morphism when every DVR valuative 2-square whose generic
1-morphism factors through that morphism has dotted-arrow category empty or a
setoid with exactly one isomorphism class.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace ValuativeCriterion.DVR.Along

/-- Every valuative 2-square whose generic 1-morphism factors through `h` and
whose ring is a discrete valuation ring has a thin dotted-arrow category with
at most one isomorphism class. -/
def Uniqueness {S : Scheme.{u}} {U X Y : GroupoidsOver S}
    [AlgebraicStack U] [AlgebraicStack X] [AlgebraicStack Y]
    (h : U ⟶ X) (f : X ⟶ Y) : Prop :=
  ∀ sq : ValuativeCommSqFactorsThrough h f, IsDiscreteValuationRing sq.sq.R →
    Quiver.IsThin (DottedArrow sq.toCone) ∧
      ∀ A A' : DottedArrow sq.toCone, Nonempty (A ≅ A')

/-- Restricted DVR uniqueness is equivalent to every factored DVR valuative
2-square having a thin dotted-arrow category with at most one isomorphism
class. -/
theorem uniqueness_iff {S : Scheme.{u}} {U X Y : GroupoidsOver S}
    [AlgebraicStack U] [AlgebraicStack X] [AlgebraicStack Y]
    (h : U ⟶ X) (f : X ⟶ Y) :
    Uniqueness h f ↔
      (∀ sq : ValuativeCommSqFactorsThrough h f, IsDiscreteValuationRing sq.sq.R →
          Quiver.IsThin (DottedArrow sq.toCone)) ∧
        ∀ sq : ValuativeCommSqFactorsThrough h f, IsDiscreteValuationRing sq.sq.R →
          ∀ A A' : DottedArrow sq.toCone, Nonempty (A ≅ A') :=
  sorry

/-- Restricted DVR uniqueness follows from thinness and a unique isomorphism
class on the dotted-arrow category of every factored DVR valuative 2-square. -/
theorem uniqueness_of {S : Scheme.{u}} {U X Y : GroupoidsOver S}
    [AlgebraicStack U] [AlgebraicStack X] [AlgebraicStack Y]
    {h : U ⟶ X} {f : X ⟶ Y}
    (h_uniqueness :
      ∀ sq : ValuativeCommSqFactorsThrough h f, IsDiscreteValuationRing sq.sq.R →
        Quiver.IsThin (DottedArrow sq.toCone) ∧
          ∀ A A' : DottedArrow sq.toCone, Nonempty (A ≅ A')) :
    Uniqueness h f :=
  sorry

/-- Restricted DVR uniqueness supplies a thin dotted-arrow category of a
factored DVR valuative 2-square. -/
theorem isThin_dottedArrow {S : Scheme.{u}} {U X Y : GroupoidsOver S}
    [AlgebraicStack U] [AlgebraicStack X] [AlgebraicStack Y]
    {h : U ⟶ X} {f : X ⟶ Y} (h_uniqueness : Uniqueness h f)
    (sq : ValuativeCommSqFactorsThrough h f)
    (hR : IsDiscreteValuationRing sq.sq.R) :
    Quiver.IsThin (DottedArrow sq.toCone) :=
  sorry

/-- Restricted DVR uniqueness supplies an isomorphism between any two dotted
arrows of a factored DVR valuative 2-square. -/
theorem nonempty_iso {S : Scheme.{u}} {U X Y : GroupoidsOver S}
    [AlgebraicStack U] [AlgebraicStack X] [AlgebraicStack Y]
    {h : U ⟶ X} {f : X ⟶ Y} (h_uniqueness : Uniqueness h f)
    (sq : ValuativeCommSqFactorsThrough h f)
    (hR : IsDiscreteValuationRing sq.sq.R)
    (A A' : DottedArrow sq.toCone) :
    Nonempty (A ≅ A') :=
  sorry

/-- Unrestricted DVR uniqueness implies DVR uniqueness along any morphism. -/
theorem of_dvrUniqueness {S : Scheme.{u}} {U X Y : GroupoidsOver S}
    [AlgebraicStack U] [AlgebraicStack X] [AlgebraicStack Y]
    (h : U ⟶ X) (f : X ⟶ Y)
    [ValuativeCriterion.DVR.Uniqueness f] :
    Uniqueness h f :=
  sorry

end ValuativeCriterion.DVR.Along

end AlgebraicGeometry.AlgebraicStack
