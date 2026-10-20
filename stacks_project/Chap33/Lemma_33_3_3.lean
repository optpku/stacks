/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Variety.Product

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CommRingCat

universe u

/- Lemma 33.3.3: the fibre product of two varieties over an algebraically closed field is a
variety. -/
@[stacks 05P3] #check
  (@AlgebraicGeometry.instVarietyPullbackOverSpecOfVarieties :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
      (X Y : Over (Spec (CommRingCat.of k))) [Variety X] [Variety Y],
      Variety (Over.mk (pullback.fst X.hom Y.hom ≫ X.hom)))
