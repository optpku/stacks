module

public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Remark_67_12_5_Opens
public import stacks_project.Chap87.Lemma_87_37_4_Completion
public import stacks_project.Chap87.Lemma_87_37_7_Types

/-!
# Types of the recompletion of a formal algebraic space

The completion of a formal algebraic space along a closed subset of its
reduction preserves locally countably indexed and locally adic* when the
open complement immersion is quasi-compact, and preserves locally Noetherian
unconditionally.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace (Points OpenSubspace)
open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

/-- Lemma 87.37.7 (1): Let `S` be a scheme. Let `X` be a formal algebraic space
over `S`. Let `T ⊆ Points (reduction X)` be a closed subset. If the open
immersion `OpenSubspace.ofOpensι T.compl` of `reduction X \ T` into
`reduction X` is quasi-compact and `X` is locally countably indexed, then the
completion `completionAlong X T` is locally countably indexed. -/
@[stacks 0GVW]
instance isLocallyCountablyIndexed_completionAlong {S : Scheme.{u}}
    {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X] [Reduction X]
    [IsLocallyCountablyIndexed X] (T : Closeds (Points (reduction X)))
    [AlgebraicSpace.QuasiCompact (OpenSubspace.ofOpensι T.compl)] :
    IsLocallyCountablyIndexed (completionAlong X T) :=
  sorry

/-- Lemma 87.37.7 (2): Let `S` be a scheme. Let `X` be a formal algebraic space
over `S`. Let `T ⊆ Points (reduction X)` be a closed subset. If the open
immersion `OpenSubspace.ofOpensι T.compl` of `reduction X \ T` into
`reduction X` is quasi-compact and `X` is locally adic*, then the completion
`completionAlong X T` is locally adic*. -/
@[stacks 0GVW]
instance isLocallyAdicStar_completionAlong {S : Scheme.{u}}
    {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X] [Reduction X]
    [IsLocallyAdicStar X] (T : Closeds (Points (reduction X)))
    [AlgebraicSpace.QuasiCompact (OpenSubspace.ofOpensι T.compl)] :
    IsLocallyAdicStar (completionAlong X T) :=
  sorry

/-- Lemma 87.37.7 (3): Let `S` be a scheme. Let `X` be a formal algebraic space
over `S`. Let `T ⊆ Points (reduction X)` be a closed subset. If `X` is locally
Noetherian, then the completion `completionAlong X T` is locally Noetherian. -/
@[stacks 0GVW]
instance isLocallyNoetherian_completionAlong {S : Scheme.{u}}
    {X : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace X] [Reduction X]
    [IsLocallyNoetherian X] (T : Closeds (Points (reduction X))) :
    IsLocallyNoetherian (completionAlong X T) :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace
