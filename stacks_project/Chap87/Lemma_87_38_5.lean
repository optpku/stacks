/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlongSubspace.Types
import StacksCheckRecall

/-!
# Types of the formal completion along a closed subspace

The formal completion of an algebraic space along a closed subspace is always
locally weakly adic, locally adic* when the closed immersion is of finite
presentation, and locally Noetherian when the ambient algebraic space is
locally Noetherian.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

/- Lemma 87.38.5 (1): Let `S` be a scheme, let `X` be an algebraic space over
`S`, and let `Z ⊂ X` be a closed subspace. The formal completion
`completionAlongSubspace i` of `X` along the closed immersion `i : Z ⟶ X` is
locally weakly adic. -/
@[stacks 0GXY]
#check (AlgebraicGeometry.AlgebraicSpace.isLocallyWeaklyAdic_completionAlongSubspace :
    ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i],
      FormalAlgebraicSpace.IsLocallyWeaklyAdic (completionAlongSubspace i))

/- Lemma 87.38.5 (2): In the situation of Lemma 87.38.5 (1), if the closed
immersion `i : Z ⟶ X` is of finite presentation, then the formal completion
along `Z` is locally adic*. -/
@[stacks 0GXY]
#check (AlgebraicGeometry.AlgebraicSpace.isLocallyAdicStar_completionAlongSubspace :
    ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
      [FinitePresentation i],
      FormalAlgebraicSpace.IsLocallyAdicStar (completionAlongSubspace i))

/- Lemma 87.38.5 (3): In the situation of Lemma 87.38.5 (1), if `X` is locally
Noetherian, then the formal completion along `Z` (written `X_Z` in the source)
is a locally Noetherian formal algebraic space. -/
@[stacks 0GXY]
#check (AlgebraicGeometry.AlgebraicSpace.isLocallyNoetherian_completionAlongSubspace :
    ∀ {S : Scheme.{u}} {X Z : AlgebraicSpace S} [IsLocallyNoetherian X]
      (i : Z ⟶ X) [IsClosedImmersion i],
      FormalAlgebraicSpace.IsLocallyNoetherian (completionAlongSubspace i))
