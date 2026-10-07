module

public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap87.Definition_87_30_1_Separation
public import stacks_project.Chap88.Definition_88_21_1
public import stacks_project.Chap88.Lemma_88_23_11
public import stacks_project.Chap88.Theorem_88_27_4

/-!
# Separatedness along the completion functor

Under the standing hypotheses of Theorem 88.27.4, a locally finite-type
morphism isomorphic over the complementary open is separated if and only if
the corresponding morphism of completions is separated and its relative
diagonal is rig-surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 88.28.3: with the standing hypotheses of Theorem 88.27.4, if
`f : X' ⟶ X` corresponds to `g : W ⟶ X_/T` under `completionFunctor X T`,
then `AlgebraicSpace.Separated f` if and only if
`FormalAlgebraicSpace.Separated g` and the relative diagonal
`pullback.diagonal g : W ⟶ W ×_{X_/T} W` is
`FormalAlgebraicSpace.RigSurjective`. The corresponding morphism is the
canonical `completionAlong.map f T`. -/
@[stacks 0ARW]
theorem completionFunctor.separated_hom_iff {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} [IsLocallyNoetherian X] (f : X' ⟶ X)
    [LocallyOfFiniteType f] (T : Closeds (Points X))
    [IsIso (openInverseImageTo f (openComplementι X T))] :
    AlgebraicSpace.Separated f ↔
      FormalAlgebraicSpace.Separated (completionAlong.map f T) ∧
        FormalAlgebraicSpace.RigSurjective
          (pullback.diagonal (completionAlong.map f T)) :=
  sorry

/-- Under the standing locally finite-type and isomorphism-over-U hypotheses of
Theorem 88.27.4, if `completionAlong.map f T` is separated and its relative
diagonal is rig-surjective, then `f` is separated. -/
theorem separated_of_completionAlongMap {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} [IsLocallyNoetherian X] (f : X' ⟶ X)
    [LocallyOfFiniteType f] (T : Closeds (Points X))
    [IsIso (openInverseImageTo f (openComplementι X T))]
    [FormalAlgebraicSpace.Separated (completionAlong.map f T)]
    [FormalAlgebraicSpace.RigSurjective
      (pullback.diagonal (completionAlong.map f T))] :
    AlgebraicSpace.Separated f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
