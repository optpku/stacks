module

public import stacks_project.Chap87.Lemma_87_14_4_Completion
public import stacks_project.Chap87.Lemma_87_38_5_Types

/-!
# Completion of an algebraic space along a closed subset

The functor of points sending a scheme `U` over `S` to the morphisms
`U ⟶ X` landing in a closed subset `T ⊆ Points X` is a formal algebraic
space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 87.14.2: Let `S` be a scheme. Let `X` be an algebraic space over `S`.
Let `T ⊆ |X|` be a closed subset. Then the functor `(Sch/S)_fppf → Sets`
sending `U` to `{ f : U ⟶ X | f(|U|) ⊆ T }` is a formal algebraic space. -/
@[stacks 0AIZ]
instance instIsFormalAlgebraicSpace_completionAlong {S : Scheme.{u}}
    (X : AlgebraicSpace S) (T : Closeds (Points X)) :
    FormalAlgebraicSpace.IsFormalAlgebraicSpace (completionAlong X T) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
