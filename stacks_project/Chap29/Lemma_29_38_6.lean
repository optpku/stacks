/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.RelativeVery
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 29.38.6: if an invertible module is relatively very ample for a scheme morphism,
then that morphism is separated. -/
@[stacks 01VQ] #check
  (AlgebraicGeometry.RelativelyVeryAmple.isSeparated :
    {X S : AlgebraicGeometry.Scheme.{u}} →
      {f : X ⟶ S} → {L : X.Modules} →
        (h : AlgebraicGeometry.RelativelyVeryAmple f L) → AlgebraicGeometry.IsSeparated f)
