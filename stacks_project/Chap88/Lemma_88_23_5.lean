module

public import stacks_project.Chap87.Lemma_87_14_5_Reduction
public import stacks_project.Chap87.Definition_87_17_4_QuasiCompact

/-!
# Quasi-compact morphisms of completions

If a morphism of algebraic spaces is quasi-compact, then the induced morphism
of formal completions along a closed subset is quasi-compact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 88.23.5: If `f : X' ⟶ X` is quasi-compact, then the induced morphism
`completionAlong.map f T` of completions along a closed subset `T` of
`Points X` is quasi-compact. -/
@[stacks 0GDE, instance]
instance quasiCompact_completionAlongMap {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} (f : X' ⟶ X) [AlgebraicSpace.QuasiCompact f]
    (T : Closeds (Points X)) :
    FormalAlgebraicSpace.QuasiCompact (completionAlong.map f T) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
