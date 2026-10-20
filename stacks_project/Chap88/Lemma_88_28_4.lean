/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.FormalModification
import StacksCheckRecall

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

/- Lemma 88.28.4: with the standing hypotheses of Theorem 88.27.4, if
`f : X' ⟶ X` corresponds to `g : W ⟶ X_/T` under `completionFunctor X T`,
then `AlgebraicSpace.Proper f` if and only if
`FormalAlgebraicSpace.FormalModification g`. The corresponding morphism is the
canonical `completionAlong.map f T`. -/
@[stacks 0ARX] #check
  (AlgebraicGeometry.AlgebraicSpace.completionFunctor.proper_hom_iff :
    ∀ {S : Scheme.{u}}
    {X X' : AlgebraicSpace S} [IsLocallyNoetherian X] (f : X' ⟶ X)
    [LocallyOfFiniteType f] (T : Closeds (Points X))
    [IsIso (openInverseImageTo f (openComplementι X T))],
    AlgebraicSpace.Proper f ↔
      FormalAlgebraicSpace.FormalModification (completionAlong.map f T))
