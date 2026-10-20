/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.IdealPower

/-!
# Ideal-power quotients of module sheaves
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The quotient module `M / I^n M` obtained as the cokernel of the inclusion of
the ideal-power product subobject. -/
abbrev idealPowerQuotient {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (M : X.Modules) (n : ℕ) : X.Modules :=
  cokernel (Modules.idealPowerProductSubobject I M n).arrow

/-- The quotient module `M / I^n M` is the cokernel of the inclusion of `I^n M`. -/
theorem idealPowerQuotient_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (I : IdealSubobject X) (M : X.Modules) (n : ℕ) :
    idealPowerQuotient I M n =
      cokernel (Modules.idealPowerProductSubobject I M n).arrow := rfl

namespace idealPowerQuotient

variable {S : Scheme.{u}} {X : AlgebraicSpace S} (I : IdealSubobject X)

/-- The canonical ideal-power quotient projection. -/
abbrev projection (M : X.Modules) (n : ℕ) : M ⟶ idealPowerQuotient I M n :=
  cokernel.π (Modules.idealPowerProductSubobject I M n).arrow

/-- A module map sends the ideal-power image into the ideal-power image of its target. -/
theorem arrow_comp_map_projection {M N : X.Modules} (f : M ⟶ N) (n : ℕ) :
    (Modules.idealPowerProductSubobject I M n).arrow ≫ f ≫ projection I N n = 0 := sorry

/-- The map of ideal-power quotients induced by a module map. -/
def map {M N : X.Modules} (f : M ⟶ N) (n : ℕ) :
    idealPowerQuotient I M n ⟶ idealPowerQuotient I N n :=
  cokernel.desc (Modules.idealPowerProductSubobject I M n).arrow
    (f ≫ projection I N n) (arrow_comp_map_projection I f n)

/-- The ideal-power quotient projection is natural in the module. -/
@[reassoc (attr := simp)]
theorem projection_map {M N : X.Modules} (f : M ⟶ N) (n : ℕ) :
    projection I M n ≫ map I f n = f ≫ projection I N n := sorry

/-- The successor ideal-power image vanishes under the preceding quotient projection. -/
theorem successor_arrow_projection (M : X.Modules) (n : ℕ) :
    (Modules.idealPowerProductSubobject I M (n + 1)).arrow ≫ projection I M n = 0 := sorry

/-- The transition between successive ideal-power quotients of a module. -/
def step (M : X.Modules) (n : ℕ) :
    idealPowerQuotient I M (n + 1) ⟶ idealPowerQuotient I M n :=
  cokernel.desc (Modules.idealPowerProductSubobject I M (n + 1)).arrow
    (projection I M n) (successor_arrow_projection I M n)

/-- Successor transitions carry the quotient projection to the preceding projection. -/
@[reassoc (attr := simp)]
theorem projection_step (M : X.Modules) (n : ℕ) :
    projection I M (n + 1) ≫ step I M n = projection I M n := sorry

end idealPowerQuotient

end AlgebraicGeometry.AlgebraicSpace
