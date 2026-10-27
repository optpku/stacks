/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlongSubspace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.LocalWeaklyAdic

/-!
# Local geometric properties of completion along a closed subspace

Completion along a closed subspace is locally weakly adic, locally adic* when
the closed immersion is of finite presentation, and locally Noetherian when
the ambient algebraic space is locally Noetherian.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The formal completion of an algebraic space along a closed immersion is
locally weakly adic. -/
instance isLocallyWeaklyAdic_completionAlongSubspace {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i] :
    FormalAlgebraicSpace.IsLocallyWeaklyAdic (completionAlongSubspace i) :=
  sorry

/-- The formal completion along a closed immersion of finite presentation is
locally adic*. -/
instance isLocallyAdicStar_completionAlongSubspace {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
    [FinitePresentation i] :
    FormalAlgebraicSpace.IsLocallyAdicStar (completionAlongSubspace i) :=
  sorry

/-- The formal completion of a locally Noetherian algebraic space along a
closed subspace is locally Noetherian. -/
instance isLocallyNoetherian_completionAlongSubspace {S : Scheme.{u}}
    {X Z : AlgebraicSpace S} [IsLocallyNoetherian X] (i : Z ⟶ X)
    [IsClosedImmersion i] :
    FormalAlgebraicSpace.IsLocallyNoetherian (completionAlongSubspace i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
