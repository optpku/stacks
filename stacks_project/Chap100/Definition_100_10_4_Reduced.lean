module

public import stacks_project.Chap100.Definition_100_10_4_Structure
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Reduction

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

namespace AlgebraicGeometry.AlgebraicStack

#check (AlgebraicGeometry.AlgebraicStack.ClosedSubstackStructure.reduced :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (Z : Closeds (Points X)), ClosedSubstackStructure Z)

#check (AlgebraicGeometry.AlgebraicStack.ClosedSubstackStructure.reduced_spec :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    (Z : Closeds (Points X)),
    Set.range (Points.map (ClosedSubstackStructure.reduced Z).ι) = Z.carrier ∧
      IsReduced (ClosedSubstackStructure.reduced Z).Y)

#check (AlgebraicGeometry.AlgebraicStack.ClosedSubstackStructure.reduced_unique :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {Z : Closeds (Points X)} (T : ClosedSubstackStructure Z),
    IsReduced T.Y → T.val = (ClosedSubstackStructure.reduced Z).val)

#check (AlgebraicGeometry.AlgebraicStack.reduction :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X], GroupoidsOver S)

#check (AlgebraicGeometry.AlgebraicStack.reductionι :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X], reduction X ⟶ X)

#check (AlgebraicGeometry.AlgebraicStack.reduction_spec :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    IsReduced (reduction X) ∧ ClosedImmersion (reductionι X) ∧
      Function.Surjective (Points.map (reductionι X)))

#check (AlgebraicGeometry.AlgebraicStack.reduction_eq_reduced_top :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    reduction X = (ClosedSubstackStructure.reduced (⊤ : Closeds (Points X))).Y)

#check (AlgebraicGeometry.AlgebraicStack.reductionι_eq_reduced_top_ι :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    reductionι X = (ClosedSubstackStructure.reduced (⊤ : Closeds (Points X))).ι)

end AlgebraicGeometry.AlgebraicStack
