/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap87.Lemma_87_14_5_Reduction
public import stacks_project.Chap87.Definition_87_17_4_QuasiCompact
public import stacks_project.Chap88.Theorem_88_27_4

/-!
# Quasi-compactness along the completion functor

Under the standing hypotheses of Theorem 88.27.4, a locally finite-type
morphism isomorphic over the complementary open is quasi-compact if and only
if the corresponding morphism of completions is quasi-compact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 88.28.1: with the standing hypotheses of Theorem 88.27.4, if
`f : X' ⟶ X` corresponds to `g : W ⟶ X_/T` under `completionFunctor X T`,
then `AlgebraicSpace.QuasiCompact f` if and only if
`FormalAlgebraicSpace.QuasiCompact g`. The corresponding morphism is the
canonical `completionAlong.map f T`. -/
@[stacks 0ARU]
theorem completionFunctor.quasiCompact_hom_iff {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} [IsLocallyNoetherian X] (f : X' ⟶ X)
    [LocallyOfFiniteType f] (T : Closeds (Points X))
    [IsIso (openInverseImageTo f (openComplementι X T))] :
    AlgebraicSpace.QuasiCompact f ↔
      FormalAlgebraicSpace.QuasiCompact (completionAlong.map f T) :=
  sorry

/-- Under the standing locally finite-type and isomorphism-over-U hypotheses of
Theorem 88.27.4, quasi-compactness of `completionAlong.map f T` implies
quasi-compactness of `f`. -/
theorem quasiCompact_of_completionAlongMap {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} [IsLocallyNoetherian X] (f : X' ⟶ X)
    [LocallyOfFiniteType f] (T : Closeds (Points X))
    [IsIso (openInverseImageTo f (openComplementι X T))]
    [FormalAlgebraicSpace.QuasiCompact (completionAlong.map f T)] :
    AlgebraicSpace.QuasiCompact f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
