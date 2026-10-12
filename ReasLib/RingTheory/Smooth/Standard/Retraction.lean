/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Smooth.StandardSmooth
public import ReasLib.RingTheory.Smooth.Retraction
import ReasLib.RingTheory.CompleteIntersection.RelativeGlobal.Retraction

/-!
# Standard-smooth retractions

This leaf refines a smooth algebra to a smooth retract extension which is
standard smooth over the original base.

@stack 07CH
-/

@[expose] public section

universe u v w

namespace Algebra

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

namespace RetractExtension

/-- A retract extension which is smooth over its source and standard smooth
over the base. -/
@[stacks 07CH "standard-smooth retract extension"]
structure StandardSmooth (R : Type u) (A : Type v) [CommRing R] [CommRing A]
    [Algebra R A] where
  /-- The underlying retract extension. -/
  base : RetractExtension.{u, v, w} R A
  /-- The extension is smooth over its source algebra. -/
  [smooth : Smooth A base.carrier]
  /-- The extension is standard smooth over the base. -/
  [standardSmooth : IsStandardSmooth R base.carrier]

attribute [instance] StandardSmooth.smooth StandardSmooth.standardSmooth

namespace StandardSmooth

/-- Refine a retract extension carrying smoothness and standard-smoothness
instances. -/
def of (E : RetractExtension.{u, v, w} R A) [Smooth A E.carrier]
    [IsStandardSmooth R E.carrier] : StandardSmooth R A where
  base := E
  smooth := inferInstance
  standardSmooth := inferInstance

/-- The retract extension supplied to `StandardSmooth.of` is recovered by
projection. -/
@[simp]
theorem base_of (E : RetractExtension.{u, v, w} R A) [Smooth A E.carrier]
    [IsStandardSmooth R E.carrier] :
    (StandardSmooth.of E).base = E := sorry

/-- The smoothness and standard-smoothness properties carried by a
standard-smooth retract extension. -/
theorem spec (E : StandardSmooth.{u, v, w} R A) :
    Smooth A E.base.carrier ∧ IsStandardSmooth R E.base.carrier := sorry

/-- Lemma 16.3.4 (tag 07CH): a smooth algebra admits a smooth retract extension
which is standard smooth over the original base. -/
@[stacks 07CH]
theorem nonempty [Smooth R A] :
    Nonempty (StandardSmooth.{u, v, max u v} R A) := sorry

end StandardSmooth

end RetractExtension

end Algebra
