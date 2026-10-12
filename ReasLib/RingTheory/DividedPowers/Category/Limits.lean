/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DividedPowers.Category
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Limits of Divided Power Rings

This module owns the limit API for `DividedPowerRing`.  The forgetful functor to commutative
rings lifts limiting cones, so the category has all small limits and those limits have the
expected underlying rings.
-/

open CategoryTheory CategoryTheory.Limits

universe v u w

namespace DividedPowerRing

namespace forgetCommRing

section

variable {J : Type v} [Category.{w} J] (K : J ⥤ DividedPowerRing.{u})

/-- Infrastructure for Lemma 23.3.2 (Tag 07GV): a limiting cone of the underlying commutative-ring
diagram lifts to a limiting cone of divided power rings. -/
@[stacks 07GV "underlying ring of a limit"]
theorem liftsLimit (c : Cone (K ⋙ DividedPowerRing.forgetCommRing)) (hc : IsLimit c) :
    Nonempty (LiftsToLimit K DividedPowerRing.forgetCommRing c hc) := sorry

/-- A lifted limiting cone may be bundled as a `LimitCone`; forgetting it recovers the supplied
limiting cone up to canonical isomorphism. -/
theorem liftsLimitCone (c : Cone (K ⋙ DividedPowerRing.forgetCommRing)) (hc : IsLimit c) :
    ∃ c' : LimitCone K,
      Nonempty (DividedPowerRing.forgetCommRing.mapCone c'.cone ≅ c) := sorry

/-- Every small diagram of divided power rings admits a limiting cone. -/
theorem existsLimitCone [Small.{u} J] : Nonempty (LimitCone K) := sorry

end

/-- Lemma 23.3.2 (Tag 07GV), part (2): the forgetful functor from divided power rings to
commutative rings creates all small limits. -/
@[stacks 07GV "underlying ring of a limit"]
instance createsLimits : CreatesLimits DividedPowerRing.forgetCommRing := sorry

end forgetCommRing

/-- Lemma 23.3.2 (Tag 07GV), part (1): the category of divided power rings has all small limits. -/
@[stacks 07GV "all limits"]
instance hasLimits : HasLimits DividedPowerRing.{u} := sorry

end DividedPowerRing
