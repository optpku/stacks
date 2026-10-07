module

public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Remark_67_12_5_Opens
public import stacks_project.Chap87.Lemma_87_14_4_Completion
public import stacks_project.Chap87.Lemma_87_38_5_Types

/-!
# Types of the formal completion along a closed subset

The formal completion of an algebraic space along a closed subset of its
points is locally adic* when the open complement immersion is quasi-compact,
and locally Noetherian when the ambient algebraic space is locally Noetherian.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The formal completion of an algebraic space along a closed subset is a
formal algebraic space. -/
instance instIsFormalAlgebraicSpace_completionAlong {S : Scheme.{u}}
    (X : AlgebraicSpace S) (T : Closeds (Points X)) :
    FormalAlgebraicSpace.IsFormalAlgebraicSpace (completionAlong X T) :=
  sorry

/-- Lemma 87.20.8 (1): Let `S` be a scheme, let `X` be an algebraic space over
`S`, and let `T ⊆ Points X` be a closed subset. If the open immersion
`OpenSubspace.ofOpensι T.compl` of `X \ T` into `X` is quasi-compact, then the
formal completion `completionAlong X T` is locally adic*. -/
@[stacks 0AQ1]
instance isLocallyAdicStar_completionAlong {S : Scheme.{u}}
    (X : AlgebraicSpace S) (T : Closeds (Points X))
    [QuasiCompact (OpenSubspace.ofOpensι T.compl)] :
    FormalAlgebraicSpace.IsLocallyAdicStar (completionAlong X T) :=
  sorry

/-- Lemma 87.20.8 (2): In the situation of Lemma 87.20.8 (1), if `X` is locally
Noetherian, then the formal completion `completionAlong X T` is a locally
Noetherian formal algebraic space. -/
@[stacks 0AQ1]
instance isLocallyNoetherian_completionAlong {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsLocallyNoetherian X] (T : Closeds (Points X)) :
    FormalAlgebraicSpace.IsLocallyNoetherian (completionAlong X T) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
