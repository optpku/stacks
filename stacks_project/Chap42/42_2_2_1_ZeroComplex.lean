/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.TwoPeriodic.Zero.Multiplicity

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory.TwoPeriodicEndomorphism

variable {R : Type u} [Ring R] {M : ModuleCat.{v} R}

#check (CategoryTheory.TwoPeriodicEndomorphism.ofZero :
  (M ⟶ M) → TwoPeriodicEndomorphism (ModuleCat R))

end CategoryTheory.TwoPeriodicEndomorphism
