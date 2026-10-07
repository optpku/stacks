module

public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap87.Definition_87_30_1_Separation
public import stacks_project.Chap87.Lemma_87_14_4_Completion

/-!
# Quasi-separated and separated morphisms of completions

If a morphism of algebraic spaces is quasi-separated or separated, then the
induced morphism of formal completions along a closed subset is likewise
quasi-separated or separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 88.23.7 (1): If `f : X' ⟶ X` is quasi-separated, then the induced
morphism `completionAlong.map f T` of completions along a closed subset `T` of
`Points X` is quasi-separated. -/
@[stacks 0GDG, instance]
instance quasiSeparated_completionAlongMap {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} (f : X' ⟶ X) [AlgebraicSpace.QuasiSeparated f]
    (T : Closeds (Points X)) :
    FormalAlgebraicSpace.QuasiSeparated (completionAlong.map f T) :=
  sorry

/-- Lemma 88.23.7 (2): If `f : X' ⟶ X` is separated, then the induced morphism
`completionAlong.map f T` of completions along a closed subset `T` of
`Points X` is separated. -/
@[stacks 0GDG, instance]
instance separated_completionAlongMap {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} (f : X' ⟶ X) [AlgebraicSpace.Separated f]
    (T : Closeds (Points X)) :
    FormalAlgebraicSpace.Separated (completionAlong.map f T) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
