/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Tor-amplitude and derived pullback

The ringed-space statement is a source-facing specialization of the generic derived pullback
construction.  The interval and object are the only mathematical inputs; ordinary additive and
derived-category structures are supplied by the canonical module-sheaf instances.
-/

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace
open scoped RingedSpace.Hom RingedSpaceDerivedPullback

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.Pullback

variable {X Y : RingedSpace.{u}}
variable [DerivedCategory.DerivedTensor.Right.Has (C := Modules X)]
variable [DerivedCategory.DerivedTensor.Right.Has (C := Modules Y)]

/-- Lemma 20.48.4: derived pullback preserves a fixed Tor-amplitude interval. -/
@[stacks 09U8]
theorem hasTorAmplitudeIn
    (f : X ⟶ Y) (E : ModuleDerived Y) {a b : ℤ}
    (hE : AlgebraicGeometry.RingedSpace.HasTorAmplitudeIn E a b) :
    AlgebraicGeometry.RingedSpace.HasTorAmplitudeIn ((L(f)^*).obj E) a b := sorry

/-- A finite Tor-dimension bound is preserved by derived pullback. -/
theorem hasFiniteTorDimension
    (f : X ⟶ Y) (E : ModuleDerived Y)
    (hE : AlgebraicGeometry.RingedSpace.HasFiniteTorDimension E) :
    AlgebraicGeometry.RingedSpace.HasFiniteTorDimension ((L(f)^*).obj E) := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived.Pullback
