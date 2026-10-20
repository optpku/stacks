/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.GenericPointPullback

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

/- Lemma 29.50.3: for a birational morphism between schemes with finitely many irreducible
components, the pullback projection over the local scheme at a target generic point is an
isomorphism. -/
@[stacks 0BAB] #check
  (AlgebraicGeometry.isIso_pullbackSnd_fromSpecStalk_of_isBirational :
    ∀ {X Y : Scheme.{u}} [Finite (irreducibleComponents X)]
      [Finite (irreducibleComponents Y)] (f : X ⟶ Y) [IsBirational f]
      (y : genericPoints Y), IsIso (pullback.snd f (Y.fromSpecStalk y)))
