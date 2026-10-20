/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Module
public import ReasLib.Algebra.Module.Length
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite length and support over a local ring
-/

@[expose] public section

universe u v

namespace Module

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- A nonzero finite module over a Noetherian local ring has support equal to the closed point
exactly when it has finite length. -/
@[stacks 00L5]
theorem support_eq_singleton_closedPoint_iff_isFiniteLength [Nontrivial M] :
    Module.support R M = ({IsLocalRing.closedPoint R} : Set (PrimeSpectrum R)) ↔
      IsFiniteLength R M := sorry

end Module
