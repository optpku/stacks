/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Definition_100_10_4_Structure
public import stacks_project.Chap100.Lemma_100_10_1
public import stacks_project.Chap100.Lemma_100_11_2_Reduced

/-!
# Reduced induced structures and reduction of algebraic stacks

Every closed subset of the points of an algebraic stack has a canonical reduced
induced structure, obtained from the unique reduced closed substack with that
point-set. The reduction of an algebraic stack is that structure on the whole
space of points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.ClosedSubstackStructure

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]

/-- The reduced induced algebraic stack structure on a closed subset of `Points X`. -/
def reduced (Z : Closeds (Points X)) : ClosedSubstackStructure Z :=
  ofSubstack (Classical.choose (ClosedSubstack.exists_reduced Z.carrier Z.isClosed))
    (Classical.choose_spec (ClosedSubstack.exists_reduced Z.carrier Z.isClosed)).1

/-- The reduced induced structure on `Z` is a reduced closed substack with
point-set `Z`. -/
theorem reduced_spec (Z : Closeds (Points X)) :
    (reduced Z).substack.pointsSet = Z.carrier ∧
      hasSmoothLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u})
        (reduced Z).Y :=
  sorry

/-- A reduced algebraic stack structure on `Z` determines the same strictly full
subcategory of `X` as the reduced induced structure. -/
theorem reduced_unique {Z : Closeds (Points X)} (T : ClosedSubstackStructure Z)
    (hT : hasSmoothLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u})
      T.Y) :
    T.substack.objectProperty = (reduced Z).substack.objectProperty :=
  sorry

/-- The reduced induced closed substack on `Z` is a reduced algebraic stack. -/
instance instIsReduced_reduced (Z : Closeds (Points X)) :
    IsReduced (reduced Z).Y :=
  sorry

end AlgebraicGeometry.AlgebraicStack.ClosedSubstackStructure

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

/-- The reduction of an algebraic stack is the reduced induced structure on its
space of points. -/
abbrev reduction (X : GroupoidsOver S) [AlgebraicStack X] : GroupoidsOver S :=
  (ClosedSubstackStructure.reduced (⊤ : Closeds (Points X))).Y

/-- The canonical closed immersion from the reduction into the original algebraic
stack. -/
abbrev reductionι (X : GroupoidsOver S) [AlgebraicStack X] : reduction X ⟶ X :=
  (ClosedSubstackStructure.reduced (⊤ : Closeds (Points X))).ι

/-- The reduction of `X` is reduced, its inclusion is a closed immersion, and that
inclusion is surjective on points. -/
theorem reduction_spec (X : GroupoidsOver S) [AlgebraicStack X] :
    hasSmoothLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u})
        (reduction X) ∧
      ClosedImmersion (reductionι X) ∧
      Function.Surjective (Points.map (reductionι X)) :=
  sorry

/-- The reduction of `X` is the underlying stack of the reduced induced structure
on `⊤`. -/
theorem reduction_eq_reduced_top (X : GroupoidsOver S) [AlgebraicStack X] :
    reduction X = (ClosedSubstackStructure.reduced (⊤ : Closeds (Points X))).Y :=
  sorry

/-- The reduction inclusion is the inclusion of the reduced induced structure on
`⊤`. -/
theorem reductionι_eq_reduced_top_ι (X : GroupoidsOver S) [AlgebraicStack X] :
    reductionι X = (ClosedSubstackStructure.reduced (⊤ : Closeds (Points X))).ι :=
  sorry

/-- The reduction of an algebraic stack is reduced. -/
instance instIsReduced_reduction (X : GroupoidsOver S) [AlgebraicStack X] :
    IsReduced (reduction X) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
