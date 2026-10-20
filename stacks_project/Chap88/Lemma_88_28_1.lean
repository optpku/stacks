/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.QuasiCompact
import StacksCheckRecall

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

/- Lemma 88.28.1: a morphism under the completion correspondence is quasi-compact
if and only if its canonical morphism of completions is quasi-compact. -/
@[stacks 0ARU] #check
  (AlgebraicGeometry.AlgebraicSpace.completionFunctor.quasiCompact_hom_iff :
    ∀ {S : Scheme.{u}} {X X' : AlgebraicSpace S} [IsLocallyNoetherian X]
      (f : X' ⟶ X) [LocallyOfFiniteType f] (T : Closeds (Points X))
      [IsIso (openInverseImageTo f (openComplementι X T))],
      AlgebraicSpace.QuasiCompact f ↔
        FormalAlgebraicSpace.ReductionData.QuasiCompact
          (completionAlong.reductionData X' (T.preimage (Points.continuous_map f)))
          (completionAlong.reductionData X T) (completionAlong.map f T))
