/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Pushforward
import Mathlib.Tactic.CrossRefAttribute

/-!
# Strongly cartesian arrows in a pushforward localization

The image of a prelocalized pushforward arrow is strongly cartesian for the pushforward
projection if its second categorical-pullback component is strongly cartesian for the original
projection. The result is independent of any topology or stack condition.

The converse claim in the proof of Stacks 04WG does not hold in general. For example, let
`C` be the chain `0 < 1`, let `S` be the chain `a < b < c`, let `p` send `a` to `0` and
`b, c` to `1`, and let `u` be the functor to the terminal category. The strongly cartesian
arrows `a ⟶ b` and `a ⟶ c` are inverted by the localization, so the image of `b ⟶ c`
is also invertible and hence strongly cartesian. But `b ⟶ c` is a noninvertible vertical
arrow for `p`, so it is not strongly cartesian.

## Main declarations

* `Functor.Pushforward.Q.map.isStronglyCartesian.ofSnd` -- the forward implication.
-/

@[expose] public section

universe uC uD uS vC vD vS

namespace CategoryTheory

open Limits
open scoped Functor

namespace Functor.Pushforward.Q

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]

/-- Lemma 8.12.6 (tag 04WG): if the second component of a prelocalized pushforward arrow is
strongly cartesian, then its image in the pushforward localization is strongly cartesian. -/
@[stacks 04WG "pushforward strongly cartesian forward criterion"]
theorem map.isStronglyCartesian.ofSnd
    (u : C ⥤ D) (p : S ⥤ C) [p.IsFibered]
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (h : ProjectionChoice u p)
    {X Y : u ₚₚ p} (f : X ⟶ Y)
    (hf : p.IsStronglyCartesian (p.map f.snd) f.snd) :
    (u.pushforwardProjection p h).IsStronglyCartesian
      ((u.pushforwardProjection p h).map ((u.pushforwardFractions p).Q.map f))
      ((u.pushforwardFractions p).Q.map f) := sorry

end Functor.Pushforward.Q

end CategoryTheory
