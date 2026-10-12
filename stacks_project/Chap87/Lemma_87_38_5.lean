/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap87.Lemma_87_38_5_Completion
public import stacks_project.Chap87.Lemma_87_38_5_Types

/-!
# Types of the formal completion along a closed subspace

The formal completion of an algebraic space along a closed subspace is always
locally weakly adic, locally adic* when the closed immersion is of finite
presentation, and locally Noetherian when the ambient algebraic space is
locally Noetherian.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The formal completion of an algebraic space along a closed immersion is a
formal algebraic space. -/
instance instIsFormalAlgebraicSpace_completionAlongSubspace {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i] :
    FormalAlgebraicSpace.IsFormalAlgebraicSpace (completionAlongSubspace i) :=
  sorry

/-- Lemma 87.38.5 (1): Let `S` be a scheme, let `X` be an algebraic space over
`S`, and let `Z ⊂ X` be a closed subspace. The formal completion
`completionAlongSubspace i` of `X` along the closed immersion `i : Z ⟶ X` is
locally weakly adic. -/
@[stacks 0GXY]
instance isLocallyWeaklyAdic_completionAlongSubspace {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i] :
    FormalAlgebraicSpace.IsLocallyWeaklyAdic (completionAlongSubspace i) :=
  sorry

/-- Lemma 87.38.5 (2): In the situation of Lemma 87.38.5 (1), if the closed
immersion `i : Z ⟶ X` is of finite presentation, then the formal completion
along `Z` is locally adic*. -/
@[stacks 0GXY]
instance isLocallyAdicStar_completionAlongSubspace {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
    [FinitePresentation i] :
    FormalAlgebraicSpace.IsLocallyAdicStar (completionAlongSubspace i) :=
  sorry

/-- Lemma 87.38.5 (3): In the situation of Lemma 87.38.5 (1), if `X` is locally
Noetherian, then the formal completion along `Z` (written `X_Z` in the source)
is a locally Noetherian formal algebraic space. -/
@[stacks 0GXY]
instance isLocallyNoetherian_completionAlongSubspace {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} [IsLocallyNoetherian X] (i : Z ⟶ X)
    [IsClosedImmersion i] :
    FormalAlgebraicSpace.IsLocallyNoetherian (completionAlongSubspace i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
