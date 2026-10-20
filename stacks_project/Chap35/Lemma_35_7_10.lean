/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation.Pushforward
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 35.7.10: for a finite morphism of finite presentation, a quasi-coherent module is
of finite presentation if and only if its pushforward is of finite presentation. -/
@[stacks 05B4] #check
  (AlgebraicGeometry.Scheme.Modules.isFinitePresentation_iff_pushforward_of_isFinite :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Scheme.Hom.FinitePresentation f]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent],
      ℱ.IsFinitePresentation ↔
        ((Scheme.Modules.pushforward f).obj ℱ).IsFinitePresentation)
