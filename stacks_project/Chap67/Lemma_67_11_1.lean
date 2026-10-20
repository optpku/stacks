/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.AtlasPushforward
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 67.11.1: For a surjective étale scheme atlas, pushforward of every
structure-sheaf module is computed by the atlas sequence, whose second arrow
is the difference of restriction along the first and second kernel-pair projections. -/
@[stacks 03M8] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.Atlas.pushforward_exact :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {U : Over S}
      (f : X ⟶ Y) (π : ofOver U ⟶ X)
      (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π)
      [Etale π] [Surjective π] (F : X.Modules),
      (AlgebraicGeometry.AlgebraicSpace.Modules.Atlas.pushforwardShortComplex f π hπ F).Exact ∧
        Mono (AlgebraicGeometry.AlgebraicSpace.Modules.Atlas.pushforwardIncl f π F))
