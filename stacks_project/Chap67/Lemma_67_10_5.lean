/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Monomorphism
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty

universe u

/- Lemma 67.10.5: the base change of a monomorphism is a monomorphism. -/
@[stacks 042P] #check
  (inferInstance :
    ∀ {S : Scheme.{u}},
      (monomorphisms (AlgebraicSpace S)).IsStableUnderBaseChange)
