module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction.Solution
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints.LocallyNoetherian
public import stacks_project.Chap98.Situation_98_27_1_Contraction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.ComplementMap
public import ReasLib.CategoryTheory.NatTrans.Arrow

/-!
# Solutions of Artin contractions

A solution for a contraction situation relative to an algebraic space `X` is a
proper morphism `f : X' ⟶ X`, a closed subset `T ⊂ |X|`, and an isomorphism
`a : X_/T ⟶ W` of formal algebraic spaces satisfying the inverse-image,
isomorphism-over-open, and completion-commutativity conditions. The restricted
functor of points of `X` on locally Noetherian schemes over `S` is the
comparison target of the contraction functor.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.Scheme.Over
open AlgebraicGeometry.AlgebraicSpace.SchemeRealization

universe u

#check (AlgebraicGeometry.AlgebraicSpace.ContractionSituation.SolutionFor :
  ∀ {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
    (σ : ContractionSituation S) (X : AlgebraicSpace S), Type (u + 1))

#check (AlgebraicGeometry.AlgebraicSpace.homOnLocallyNoetherian :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type (u + 1))
