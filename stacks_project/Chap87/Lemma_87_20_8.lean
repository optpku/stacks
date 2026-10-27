/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.Types
import StacksCheckRecall

/-!
# Types of the formal completion along a closed subset

The formal completion of an algebraic space along a closed subset of its
points is locally adic* when the open complement immersion is quasi-compact,
and locally Noetherian when the ambient algebraic space is locally Noetherian.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- The formal completion of an algebraic space along a closed subset is a
formal algebraic space. -/
#check (AlgebraicGeometry.AlgebraicSpace.instIsFormalAlgebraicSpace_completionAlong :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) (T : Closeds (Points X)),
    FormalAlgebraicSpace.IsFormalAlgebraicSpace (completionAlong X T))

/- Lemma 87.20.8 (1): Let `S` be a scheme, let `X` be an algebraic space over
`S`, and let `T ⊆ Points X` be a closed subset. If the open immersion
`OpenSubspace.Construction.ι X T.compl` of `X \ T` into `X` is quasi-compact, then the
formal completion `completionAlong X T` is locally adic*. -/
@[stacks 0AQ1] #check (AlgebraicGeometry.AlgebraicSpace.isLocallyAdicStar_completionAlong :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) (T : Closeds (Points X)),
    [QuasiCompact (OpenSubspace.Construction.ι X T.compl)] →
    FormalAlgebraicSpace.IsLocallyAdicStar (completionAlong X T))

/- Lemma 87.20.8 (2): In the situation of Lemma 87.20.8 (1), if `X` is locally
Noetherian, then the formal completion `completionAlong X T` is a locally
Noetherian formal algebraic space. -/
@[stacks 0AQ1] #check (AlgebraicGeometry.AlgebraicSpace.instIsLocallyNoetherian_completionAlong :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S), [IsLocallyNoetherian X] →
    ∀ (T : Closeds (Points X)),
    FormalAlgebraicSpace.IsLocallyNoetherian (completionAlong X T))

end AlgebraicGeometry.AlgebraicSpace
