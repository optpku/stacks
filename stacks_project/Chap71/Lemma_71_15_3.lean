/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Ample.Relative.Proper

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory CategoryTheory.MonoidalCategory

universe u

/- Lemma 71.15.3: for a more general version see Descent on Spaces, Lemma 74.13.2.
An invertible module that is ample on a scheme-theoretic fibre of a proper
morphism of algebraic spaces over a Noetherian scheme is relatively ample over
some open neighbourhood of that point. -/
@[stacks 0D3A] #check
  (AlgebraicGeometry.AlgebraicSpace.RelativelyAmple.exists_morphismRestrict_of_isAmple_fiber :
    ∀ {Y : Scheme.{u}} [IsNoetherian Y] {X : AlgebraicSpace Y}
      (f : X ⟶ ofOver (Over.mk (𝟙 Y))) [Proper f]
      (L : X.Modules) [isInvertibleObject L] (y : Y)
      {T : Over Y} (e : fiber f y ≅ ofOver T)
      [Scheme.Modules.IsAmple (moduleOnScheme f y e L)],
      ∃ V : Y.Opens, y ∈ V ∧
        RelativelyAmple (morphismRestrict f V)
          (Modules.restrictToBasePreimage f L V))
