module

public import stacks_project.Chap87.Lemma_87_14_4_Completion
public import stacks_project.Chap88.Definition_88_20_1_Etale

/-!
# Étale morphisms of completions

If a morphism of algebraic spaces is étale, then the induced morphism of
formal completions along a closed subset is étale.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 88.23.2: If `f : X' ⟶ X` is étale, then the induced morphism
`completionAlong.map f T` of completions along a closed subset `T` of
`Points X` is étale. -/
@[stacks 0GI0, instance]
instance etale_completionAlongMap {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (f : X' ⟶ X) [AlgebraicSpace.Etale f] (T : Closeds (Points X)) :
    FormalAlgebraicSpace.Etale (completionAlong.map f T) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
