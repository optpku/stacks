module

public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap87.Definition_87_30_1_Separation
public import stacks_project.Chap88.Theorem_88_27_4

/-!
# Quasi-separatedness along the completion functor

Under the standing hypotheses of Theorem 88.27.4, a locally finite-type
morphism isomorphic over the complementary open is quasi-separated if and only
if the corresponding morphism of completions is quasi-separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 88.28.2: with the standing hypotheses of Theorem 88.27.4, if
`f : X' ⟶ X` corresponds to `g : W ⟶ X_/T` under `completionFunctor X T`,
then `AlgebraicSpace.QuasiSeparated f` if and only if
`FormalAlgebraicSpace.QuasiSeparated g`. The corresponding morphism is the
canonical `completionAlong.map f T`. -/
@[stacks 0ARV]
theorem completionFunctor.quasiSeparated_hom_iff {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} [IsLocallyNoetherian X] (f : X' ⟶ X)
    [LocallyOfFiniteType f] (T : Closeds (Points X))
    [IsIso (openInverseImageTo f (openComplementι X T))] :
    AlgebraicSpace.QuasiSeparated f ↔
      FormalAlgebraicSpace.QuasiSeparated (completionAlong.map f T) :=
  sorry

/-- Under the standing locally finite-type and isomorphism-over-U hypotheses of
Theorem 88.27.4, quasi-separatedness of `completionAlong.map f T` implies
quasi-separatedness of `f`. -/
theorem quasiSeparated_of_completionAlongMap {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} [IsLocallyNoetherian X] (f : X' ⟶ X)
    [LocallyOfFiniteType f] (T : Closeds (Points X))
    [IsIso (openInverseImageTo f (openComplementι X T))]
    [FormalAlgebraicSpace.QuasiSeparated (completionAlong.map f T)] :
    AlgebraicSpace.QuasiSeparated f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
