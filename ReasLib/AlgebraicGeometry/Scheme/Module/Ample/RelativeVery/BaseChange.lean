/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.RelativeVery
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Base change of relatively very ample modules

Relative very ampleness of scheme modules is preserved by cartesian base change.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- Pulling a relatively very ample module back around a cartesian square preserves relative very
ampleness. -/
@[stacks 0B3F "relative very ampleness under base change"]
theorem RelativelyVeryAmple.of_isPullback
    {S X S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} {L : X.Modules}
    (sq : IsPullback g' f' f g) (hL : RelativelyVeryAmple f L) :
    RelativelyVeryAmple f' ((Scheme.Modules.pullback g').obj L) := sorry

/-- The pullback of a relatively very ample module along the canonical projection is relatively
very ample over the other projection. -/
instance instRelativelyVeryAmplePullback
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (L : X.Modules)
    [hL : RelativelyVeryAmple f L] :
    RelativelyVeryAmple (pullback.snd f g)
      ((Scheme.Modules.pullback (pullback.fst f g)).obj L) :=
  RelativelyVeryAmple.of_isPullback (IsPullback.of_hasPullback f g) hL

end AlgebraicGeometry
