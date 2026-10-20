/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.FinitePresentation
import StacksCheckRecall

open AlgebraicGeometry

universe u

/- Lemma 29.30.6: a syntomic morphism is locally of finite presentation. -/
@[stacks 01UK] #check (AlgebraicGeometry.Syntomic.locallyOfFinitePresentation :
    ∀ {X S : Scheme.{u}} {f : X ⟶ S}, AlgebraicGeometry.Syntomic f →
      AlgebraicGeometry.LocallyOfFinitePresentation f)
