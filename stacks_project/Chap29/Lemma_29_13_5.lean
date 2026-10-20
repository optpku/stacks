/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiAffine.Operations
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u

/- Lemma 29.13.5: quasi-affineness is stable under arbitrary base change. -/
@[stacks 01SO] #check
  (AlgebraicGeometry.QuasiAffineHom.baseChange :
    ∀ {X S S' : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S} (g : S' ⟶ S),
      AlgebraicGeometry.QuasiAffineHom f →
        AlgebraicGeometry.QuasiAffineHom (pullback.snd f g))
