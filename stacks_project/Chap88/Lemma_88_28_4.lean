module

public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap88.Definition_88_24_1_Modification
public import stacks_project.Chap88.Lemma_88_23_1
public import stacks_project.Chap88.Theorem_88_27_4

/-!
# Properness along the completion functor

Under the standing hypotheses of Theorem 88.27.4, a locally finite-type
morphism isomorphic over the complementary open is proper if and only if the
corresponding morphism of completions is a formal modification.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 88.28.4: with the standing hypotheses of Theorem 88.27.4, if
`f : X' ⟶ X` corresponds to `g : W ⟶ X_/T` under `completionFunctor X T`,
then `AlgebraicSpace.Proper f` if and only if
`FormalAlgebraicSpace.FormalModification g`. The corresponding morphism is the
canonical `completionAlong.map f T`. -/
@[stacks 0ARX]
theorem completionFunctor.proper_hom_iff {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} [IsLocallyNoetherian X] (f : X' ⟶ X)
    [LocallyOfFiniteType f] (T : Closeds (Points X))
    [IsIso (openInverseImageTo f (openComplementι X T))] :
    AlgebraicSpace.Proper f ↔
      FormalAlgebraicSpace.FormalModification (completionAlong.map f T) :=
  sorry

/-- Under the standing locally finite-type and isomorphism-over-U hypotheses of
Theorem 88.27.4, if `completionAlong.map f T` is a formal modification, then
`f` is proper. -/
theorem proper_of_completionAlongMap {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} [IsLocallyNoetherian X] (f : X' ⟶ X)
    [LocallyOfFiniteType f] (T : Closeds (Points X))
    [IsIso (openInverseImageTo f (openComplementι X T))]
    [FormalAlgebraicSpace.FormalModification (completionAlong.map f T)] :
    AlgebraicSpace.Proper f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
