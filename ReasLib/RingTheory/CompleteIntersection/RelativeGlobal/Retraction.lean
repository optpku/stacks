/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Smooth.Basic
import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CompleteIntersection.RelativeGlobal.Basic
public import ReasLib.RingTheory.RingHom.Syntomic.Basic
public import ReasLib.RingTheory.Smooth.Retraction

/-!
# Relative complete-intersection retractions

@stack 07CG

This leaf constructs smooth retract extensions of syntomic algebras whose
composite over the original base is a relative global complete intersection.
-/

@[expose] public section

universe u v w

namespace Algebra

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

namespace RetractExtension

/-- A retract extension which is smooth over its source, flat over the base,
and a relative global complete intersection over the base. -/
@[stacks 07CG "relative complete-intersection retract extension"]
structure RelativeCI (R : Type u) (A : Type v) [CommRing R] [CommRing A]
    [Algebra R A] where
  /-- The underlying retract extension. -/
  base : RetractExtension.{u, v, w} R A
  /-- The extension is smooth over its source algebra. -/
  [smooth : Smooth A base.carrier]
  /-- The extension is flat over the original base ring. -/
  [flat : Module.Flat R base.carrier]
  /-- The extension is a relative global complete intersection over the base. -/
  [relativeCI : IsRelativeGlobalCompleteIntersection R base.carrier]

attribute [instance] RelativeCI.smooth RelativeCI.flat RelativeCI.relativeCI

namespace RelativeCI

/-- Refine a retract extension carrying smoothness, base flatness, and relative
complete-intersection instances. -/
def of (E : RetractExtension.{u, v, w} R A) [Smooth A E.carrier]
    [Module.Flat R E.carrier]
    [IsRelativeGlobalCompleteIntersection R E.carrier] : RelativeCI R A where
  base := E
  smooth := inferInstance
  flat := inferInstance
  relativeCI := inferInstance

/-- The retract extension supplied to `RelativeCI.of` is recovered by
projection. -/
@[simp]
theorem base_of (E : RetractExtension.{u, v, w} R A) [Smooth A E.carrier]
    [Module.Flat R E.carrier]
    [IsRelativeGlobalCompleteIntersection R E.carrier] :
    (RelativeCI.of E).base = E := sorry

/-- The smoothness, base flatness, and relative complete-intersection
properties carried by a relative complete-intersection retract extension. -/
theorem spec (E : RelativeCI.{u, v, w} R A) :
    Smooth A E.base.carrier ∧
      Module.Flat R E.base.carrier ∧
        IsRelativeGlobalCompleteIntersection R E.base.carrier := sorry

/-- Lemma 16.3.3 (tag 07CG): a syntomic algebra admits a smooth retract
extension which is flat and a relative global complete intersection over the
base. -/
@[stacks 07CG]
theorem nonempty (hA : (algebraMap R A).Syntomic) :
    Nonempty (RelativeCI.{u, v, max u v} R A) := sorry

end RelativeCI

namespace Smoothing

/-- A smoothing retract of a syntomic algebra is smooth over that algebra. -/
@[stacks 07CG "smoothing retract is smooth over its source"]
theorem smoothBase (S : Smoothing.{u, v, w} R A)
    (hA : (algebraMap R A).Syntomic) :
    Smooth A S.base.carrier := sorry

/-- A smoothing retract of a syntomic algebra is flat over the original base
ring. -/
@[stacks 07CG "smoothing retract is flat over the base"]
theorem flatBase (S : Smoothing.{u, v, w} R A)
    (hA : (algebraMap R A).Syntomic) :
    Module.Flat R S.base.carrier := sorry

/-- A smoothing retract of a syntomic algebra is a relative global complete
intersection over the original base. -/
@[stacks 07CG "smoothing retract is a relative complete intersection"]
theorem relativeCIBase (S : Smoothing.{u, v, w} R A)
    (hA : (algebraMap R A).Syntomic) :
    IsRelativeGlobalCompleteIntersection R S.base.carrier := sorry

/-- Regard a smoothing retract of a syntomic algebra as a relative
complete-intersection retract. -/
@[stacks 07CG "smoothing retract to relative complete-intersection retract"]
def toRelativeCI (S : Smoothing.{u, v, w} R A)
    (hA : (algebraMap R A).Syntomic) :
    RelativeCI R A where
  base := S.base
  smooth := S.smoothBase hA
  flat := S.flatBase hA
  relativeCI := S.relativeCIBase hA

end Smoothing

end RetractExtension

end Algebra
