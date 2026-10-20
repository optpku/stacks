/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.SmoothGroupoid
public import ReasLib.AlgebraicGeometry.FormalDeformation.SmoothPowerSeries

/-!
# Smoothness and power series for prorepresentable groupoids

The restricted coyoneda maps induced by two parallel complete local algebra maps
are smooth exactly when both maps are finite-variable power series extensions.
-/

@[expose] public section

open CategoryTheory
open CompleteLocalAlgCat

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.GroupoidInFunctors

/-- Two parallel maps of complete local algebras induce smooth groupoid structure
maps on restricted coyoneda functors if and only if the target is a finite-variable
power series algebra over the source along each map. -/
@[stacks 06KK]
theorem isSmooth_iff_isPowerSeriesOver {R0 R1 : CompleteLocalAlgCat Λ k}
    (s t : R0 ⟶ R1) :
    IsSmooth (restrictedCoyonedaMap s) (restrictedCoyonedaMap t) ↔
      IsPowerSeriesOver s ∧ IsPowerSeriesOver t :=
  sorry

end CategoryTheory.GroupoidInFunctors
