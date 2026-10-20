/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.Monomorphism
import StacksCheckRecall

/- Lemma 35.25.1: a flat, quasi-compact, surjective monomorphism of schemes is an
isomorphism. -/
@[stacks 06NC] #check
  (AlgebraicGeometry.Flat.isIso_of_quasiCompact_surjective_mono :
    ∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y)
      [AlgebraicGeometry.Flat f] [AlgebraicGeometry.QuasiCompact f]
      [AlgebraicGeometry.Surjective f] [CategoryTheory.Mono f], CategoryTheory.IsIso f)
