/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import ReasLib.LinearAlgebra.LinearMap.Factorisation.FiniteProjective

@[expose] public section

/-!
# Duals of finite-projective factorisations

@stack 0G96
-/

universe u v w

namespace LinearMap

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]
variable {N : Type w} [AddCommMonoid N] [Module R N]
variable {f : M →ₗ[R] N}

namespace Factorisation.FiniteProjective

/-- The dual midpoint of a finite-projective factorisation is finite projective. -/
theorem dual_property (F : Factorisation.FiniteProjective f) :
    Module.FiniteProjective R (Module.Dual R F.mid) := sorry

/-- The triangle equation obtained by dualizing a finite-projective factorisation. -/
theorem dualMap_factor (F : Factorisation.FiniteProjective f) :
    F.fromSource.dualMap.comp F.toTarget.dualMap = f.dualMap := sorry

/-- Dualize a finite-projective factorisation, reversing its source and target. -/
def dualMap (F : Factorisation.FiniteProjective f) :
    Factorisation.FiniteProjective f.dualMap where
  base :=
    { mid := SemimoduleCat.of R (Module.Dual R F.mid)
      fromSource := F.toTarget.dualMap
      toTarget := F.fromSource.dualMap
      factor := dualMap_factor F }
  property := dual_property F

end Factorisation.FiniteProjective

/-- Dualization preserves factorisation through a finite projective module. -/
theorem FactorsThroughFiniteProjective.dualMap
    (hf : f.FactorsThroughFiniteProjective) : f.dualMap.FactorsThroughFiniteProjective := sorry

/-- The dual of scalar multiplication is scalar multiplication on the dual module. -/
@[simp]
theorem dualMap_lsmul (a : R) :
    (LinearMap.lsmul R M a).dualMap = LinearMap.lsmul R (Module.Dual R M) a := sorry

end LinearMap
