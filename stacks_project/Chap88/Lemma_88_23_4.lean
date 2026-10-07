module

public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap87.Lemma_87_14_4_Completion
public import stacks_project.Chap88.Lemma_88_23_4_Proper

/-!
# Proper morphisms of completions

If a morphism of algebraic spaces is proper, then the induced morphism of
formal completions along a closed subset is proper.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 88.23.4: If `f : X' ⟶ X` is proper, then the induced morphism
`completionAlong.map f T` of completions along a closed subset `T` of
`Points X` is proper. -/
@[stacks 0GDD, instance]
instance proper_completionAlongMap {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} (f : X' ⟶ X) [AlgebraicSpace.Proper f]
    (T : Closeds (Points X)) :
    FormalAlgebraicSpace.Proper (completionAlong.map f T) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
