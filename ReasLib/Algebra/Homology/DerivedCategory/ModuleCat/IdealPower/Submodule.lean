module

public import ReasLib.Algebra.Homology.DerivedCategory.TensorProduct
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleEmbedding
public import ReasLib.Algebra.Module.IdealPower.Submodule.Sequential
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived systems of ideal-power submodules

This leaf places the positive adic submodule system in degree zero.  It provides
the module-parametric system, its regular-module specialization `(I ^ (n + 1))[0]`,
and the fixed-right derived-tensor system used by adic comparison arguments.
@stack 0G3M
@stack 0G3N
-/

@[expose] public section

open CategoryTheory
open Opposite

noncomputable section

universe u v

namespace CategoryTheory.DerivedCategory.IdealPower.Submodule

variable {A : Type u} [CommRing A]

/- The zero-based index here denotes the positive exponent `n + 1`; keeping it in a nested
namespace prevents accidental mixing with `Ideal.PowerSubmodule.stage`, whose index starts at `I⁰`. -/
namespace Positive

/-- The positive adic stage `(I ^ (n + 1) M)[0]` in the derived category. -/
@[stacks 0G3M "positive adic submodule derived stage"]
abbrev stage
    (I : Ideal A) (M : ModuleCat.{v} A) (n : ℕ) :
    DerivedCategory (ModuleCat.{v} A) :=
  ModuleCat.single0 (Ideal.PowerSubmodule.positiveStageObj I M n)

/-- The derived successor transition
`(I ^ (n + 2) M)[0] ⟶ (I ^ (n + 1) M)[0]`. -/
@[stacks 0G3M "positive adic submodule derived transition"]
abbrev step
    (I : Ideal A) (M : ModuleCat.{v} A) (n : ℕ) :
    stage I M (n + 1) ⟶ stage I M n :=
  ModuleCat.single0Functor.map (Ideal.PowerSubmodule.positiveStep I M n)

/-- The positive adic submodule system placed in degree zero. -/
@[stacks 0G3M "positive adic submodule derived system"]
abbrev system
    (I : Ideal A) (M : ModuleCat.{v} A) :
    SequentialInverseSystem (DerivedCategory (ModuleCat.{v} A)) :=
  Functor.ofOpSequence (step I M)

/-- The `n`th regular-module stage `(I ^ (n + 1))[0]`. -/
@[stacks 0G3M "positive ideal-power derived stage"]
abbrev regularStage (I : Ideal A) (n : ℕ) :
    DerivedCategory (ModuleCat A) :=
  stage I (ModuleCat.of A A) n

/-- The successor transition `(I ^ (n + 2))[0] ⟶ (I ^ (n + 1))[0]`. -/
@[stacks 0G3M "positive ideal-power derived transition"]
abbrev regularStep (I : Ideal A) (n : ℕ) :
    regularStage I (n + 1) ⟶ regularStage I n :=
  step I (ModuleCat.of A A) n

/-- The positive regular ideal-power system `((I ^ (n + 1))[0])ₙ`. -/
@[stacks 0G3M "positive ideal-power derived system"]
abbrev regularSystem (I : Ideal A) :
    SequentialInverseSystem (DerivedCategory (ModuleCat A)) :=
  system I (ModuleCat.of A A)

/-- The fixed-right derived-tensor system `((I ^ (n + 1))[0] ⊗ᴸ K)ₙ`. -/
@[stacks 0G3N "positive ideal-power derived tensor system"]
abbrev tensorSystem
    (I : Ideal A) (K : DerivedCategory (ModuleCat A)) :
    SequentialInverseSystem (DerivedCategory (ModuleCat A)) :=
  regularSystem I ⋙ derivedTensorProduct K

/-- The object formula for the positive adic derived system. -/
@[simp, stacks 0G3M "positive adic submodule derived system object"]
theorem system_obj
    (I : Ideal A) (M : ModuleCat.{v} A) (n : ℕ) :
    (system I M).obj (op n) = stage I M n := sorry

/-- The successor-map formula for the positive adic derived system. -/
@[simp, stacks 0G3M "positive adic submodule derived system transition"]
theorem system_stepMap
    (I : Ideal A) (M : ModuleCat.{v} A) (n : ℕ) :
    (system I M).stepMap n = step I M n := sorry

/-- Placing the module-level positive system in degree zero recovers the derived system. -/
@[stacks 0G3M "degree-zero image of the positive adic submodule system"]
theorem system_eq_map (I : Ideal A) (M : ModuleCat.{v} A) :
    system I M =
      Ideal.PowerSubmodule.positiveSystem I M ⋙ ModuleCat.single0Functor := sorry

/-- The object formula for the regular ideal-power derived system. -/
@[simp, stacks 0G3M "positive ideal-power derived system object"]
theorem regularSystem_obj (I : Ideal A) (n : ℕ) :
    (regularSystem I).obj (op n) = regularStage I n := sorry

/-- The successor-map formula for the regular ideal-power derived system. -/
@[simp, stacks 0G3M "positive ideal-power derived system transition"]
theorem regularSystem_stepMap (I : Ideal A) (n : ℕ) :
    (regularSystem I).stepMap n = regularStep I n := sorry

/-- The object formula for the fixed-right ideal-power derived tensor system. -/
@[simp, stacks 0G3N "positive ideal-power derived tensor system object"]
theorem tensorSystem_obj
    (I : Ideal A) (K : DerivedCategory (ModuleCat A)) (n : ℕ) :
    (tensorSystem I K).obj (op n) =
      (derivedTensorProduct K).obj (regularStage I n) := sorry

/-- The successor-map formula for the fixed-right ideal-power derived tensor system. -/
@[simp, stacks 0G3N "positive ideal-power derived tensor system transition"]
theorem tensorSystem_stepMap
    (I : Ideal A) (K : DerivedCategory (ModuleCat A)) (n : ℕ) :
    (tensorSystem I K).stepMap n =
      (derivedTensorProduct K).map (regularStep I n) := sorry

end Positive

end CategoryTheory.DerivedCategory.IdealPower.Submodule
