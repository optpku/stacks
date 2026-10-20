/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Base change of relatively ample modules

Relative ampleness of scheme modules is preserved by cartesian base change.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- Pulling a relatively ample module back around a cartesian square preserves relative
ampleness. -/
theorem RelativelyAmple.of_isPullback
    {S X S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {L : X.Modules}
    (sq : IsPullback g' f' f g) (hL : RelativelyAmple f L) :
    RelativelyAmple f' ((Scheme.Modules.pullback g').obj L) := sorry

/-- The pullback of a relatively ample module along the canonical projection is relatively
ample over the other projection. -/
instance instRelativelyAmplePullback
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (L : X.Modules)
    [hL : RelativelyAmple f L] :
    RelativelyAmple (pullback.snd f g)
      ((Scheme.Modules.pullback (pullback.fst f g)).obj L) :=
  RelativelyAmple.of_isPullback (IsPullback.of_hasPullback f g) hL

end AlgebraicGeometry
