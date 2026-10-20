/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.IdealPower.Quotient
public import ReasLib.Algebra.Module.IdealPower.Submodule
public import ReasLib.CategoryTheory.InverseSystem.Sequential
import Mathlib.RingTheory.AdicCompletion.Basic

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace Ideal.PowerQuotient

variable {A : Type u} [CommRing A]

/-- The inverse system whose stage `n` is the exact quotient `M / I ^ n M`. -/
noncomputable def system (I : Ideal A) (M : ModuleCat.{u} A) :
    SequentialInverseSystem (ModuleCat.{u} A) :=
  Functor.ofOpSequence (X := fun n ↦ stage I M n)
    (fun n ↦ ModuleCat.ofHom
      (AdicCompletion.transitionMap I (M : Type u) (Nat.le_succ n)))

/-- The object at index `n` of the exact ideal-power quotient system. -/
@[simp]
theorem system_obj (I : Ideal A) (M : ModuleCat.{u} A) (n : ℕ) :
    (system I M).obj (op n) = stage I M n := sorry

/-- The successor map of the exact ideal-power quotient system. -/
theorem system_stepMap (I : Ideal A) (M : ModuleCat.{u} A) (n : ℕ) :
    (system I M).stepMap n =
      ModuleCat.ofHom (AdicCompletion.transitionMap I (M : Type u) (Nat.le_succ n)) := sorry

end Ideal.PowerQuotient

namespace Ideal.PowerSubmodule

variable {A : Type u} [CommRing A]

/-- The quotient of the `m`th adic stage by the `n`th adic stage. -/
noncomputable def quotientStage
    (I : Ideal A) (M : ModuleCat.{u} A) (m n : ℕ) : ModuleCat.{u} A :=
  ModuleCat.of A
    ((stage I (M : Type u) m) ⧸
      (stage I (M : Type u) n).comap (subtype I (M : Type u) m))

/-- The quotient map from the next denominator stage to the current denominator stage. -/
noncomputable def quotientStep
    (I : Ideal A) (M : ModuleCat.{u} A) (m n : ℕ) :
    quotientStage I M m (n + 1) ⟶ quotientStage I M m n :=
  ModuleCat.ofHom
    (Submodule.factor (Submodule.comap_mono (stage_antitone I (Nat.le_succ n))))

/-- The fixed-numerator quotient system with stage `n` equal to `I ^ m M / I ^ (m + n) M`. -/
noncomputable def quotientSystem
    (I : Ideal A) (M : ModuleCat.{u} A) (m : ℕ) :
    SequentialInverseSystem (ModuleCat.{u} A) :=
  Functor.ofOpSequence (X := fun n ↦ quotientStage I M m (m + n))
    (fun n ↦ quotientStep I M m (m + n))

/-- The quotient map from the `m`th adic stage to a fixed-numerator quotient stage. -/
noncomputable def quotientMap
    (I : Ideal A) (M : ModuleCat.{u} A) (m n : ℕ) :
    stageObj I M m ⟶ quotientStage I M m (m + n) :=
  ModuleCat.ofHom
    ((stage I (M : Type u) (m + n)).comap (subtype I (M : Type u) m)).mkQ

/-- The object formula for the fixed-numerator quotient system. -/
theorem quotientSystem_obj
    (I : Ideal A) (M : ModuleCat.{u} A) (m n : ℕ) :
    (quotientSystem I M m).obj (op n) = quotientStage I M m (m + n) := sorry

end Ideal.PowerSubmodule
