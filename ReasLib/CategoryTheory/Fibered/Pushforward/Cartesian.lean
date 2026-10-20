module

public import ReasLib.CategoryTheory.Fibered.Pushforward
import Mathlib.Tactic.CrossRefAttribute

/-!
# Strongly cartesian arrows in a pushforward localization

This module characterizes the image of a prelocalized pushforward arrow under the localization
functor.  Its image is strongly cartesian for the pushforward projection exactly when the
arrow's second categorical-pullback component is strongly cartesian for the original
projection.  The result is independent of any topology or stack condition.

## Main declarations

* `Functor.Pushforward.Q.map.isStronglyCartesian.ofSnd` -- the forward implication.
* `Functor.Pushforward.Q.snd.isStronglyCartesian.ofMap` -- reflection to the second component.
* `Functor.Pushforward.Q.map.isStronglyCartesian.iffSnd` -- the componentwise criterion.
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

/-- Lemma 8.12.6 (tag 04WG): if the image of a prelocalized pushforward arrow is strongly
cartesian in the pushforward localization, then its second component is strongly cartesian. -/
@[stacks 04WG "pushforward strongly cartesian reflection criterion"]
theorem snd.isStronglyCartesian.ofMap
    (u : C ⥤ D) (p : S ⥤ C) [p.IsFibered]
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (h : ProjectionChoice u p)
    {X Y : u ₚₚ p} (f : X ⟶ Y)
    (hf : (u.pushforwardProjection p h).IsStronglyCartesian
      ((u.pushforwardProjection p h).map ((u.pushforwardFractions p).Q.map f))
      ((u.pushforwardFractions p).Q.map f)) :
    p.IsStronglyCartesian (p.map f.snd) f.snd := sorry

/-- Lemma 8.12.6 (tag 04WG): the image of a prelocalized pushforward arrow is strongly
cartesian exactly when its second categorical-pullback component is strongly cartesian. -/
@[stacks 04WG "pushforward strongly cartesian component criterion"]
theorem map.isStronglyCartesian.iffSnd
    (u : C ⥤ D) (p : S ⥤ C) [p.IsFibered]
    [HasPullbacks C] [HasEqualizers C]
    [PreservesLimitsOfShape WalkingCospan u]
    [PreservesLimitsOfShape WalkingParallelPair u]
    (h : ProjectionChoice u p)
    {X Y : u ₚₚ p} (f : X ⟶ Y) :
    (u.pushforwardProjection p h).IsStronglyCartesian
      ((u.pushforwardProjection p h).map ((u.pushforwardFractions p).Q.map f))
      ((u.pushforwardFractions p).Q.map f) ↔
      p.IsStronglyCartesian (p.map f.snd) f.snd := sorry

end Functor.Pushforward.Q

end CategoryTheory
