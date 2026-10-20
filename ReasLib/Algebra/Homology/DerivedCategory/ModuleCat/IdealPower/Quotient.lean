module

public import ReasLib.Algebra.Homology.DerivedCategory.TensorProduct
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleEmbedding
public import ReasLib.Algebra.Module.IdealPower.Quotient
public import ReasLib.CategoryTheory.InverseSystem.Sequential
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived ideal-power quotient towers

This leaf owns the derived tower of the positive quotients
`(A ⧸ I ^ (n + 1))[0]` and its fixed-right derived-tensor specialization.  The
concrete quotient stages are shared with the module-level `Ideal.PowerQuotient`
owner; chapter files only provide source-specific comparison maps and results.

@stack 0922
-/

@[expose] public section

open CategoryTheory
open Opposite

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IdealPower

variable {A : Type u} [CommRing A]

/-- The `n`th derived stage of the positive ideal-power quotient tower,
`(A ⧸ I ^ (n + 1))[0]`. -/
@[stacks 0922 "positive ideal-power quotient derived stage"]
abbrev stage (I : Ideal A) (n : ℕ) : DerivedCategory (ModuleCat A) :=
  ModuleCat.single0
    (Ideal.PowerQuotient.positiveStage I (ModuleCat.of A A) n)

/-- The successor transition `(A ⧸ I ^ (n + 2))[0] ⟶
(A ⧸ I ^ (n + 1))[0]` in the derived category. -/
@[stacks 0922 "positive ideal-power quotient derived transition"]
abbrev step (I : Ideal A) (n : ℕ) : stage I (n + 1) ⟶ stage I n :=
  ModuleCat.single0Functor.map
    (Ideal.PowerQuotient.positiveStep I (ModuleCat.of A A) n)

/-- The sequential inverse system of positive ideal-power quotient stages. -/
@[stacks 0922 "positive ideal-power quotient derived system"]
abbrev system (I : Ideal A) :
    SequentialInverseSystem (DerivedCategory (ModuleCat A)) :=
  Ideal.PowerQuotient.positiveSystem I (ModuleCat.of A A) ⋙
    ModuleCat.single0Functor

/-- The fixed-right derived-tensor tower
`((A ⧸ I ^ (n + 1))[0] ⊗ᴸ K)_n`. -/
@[stacks 0922 "positive ideal-power quotient derived tensor system"]
abbrev tensorSystem (I : Ideal A) (K : DerivedCategory (ModuleCat A)) :
    SequentialInverseSystem (DerivedCategory (ModuleCat A)) :=
  system I ⋙ derivedTensorProduct K

/-- The object formula for the positive ideal-power derived system. -/
@[simp, stacks 0922 "positive ideal-power derived system object"]
theorem system_obj (I : Ideal A) (n : ℕ) :
    (system I).obj (op n) = stage I n := sorry

/-- The successor map formula for the positive ideal-power derived system. -/
@[simp, stacks 0922 "positive ideal-power derived system transition"]
theorem system_stepMap (I : Ideal A) (n : ℕ) :
    (system I).stepMap n = step I n := sorry

/-- The object formula after tensoring the ideal-power system with `K`. -/
@[simp, stacks 0922 "positive ideal-power derived tensor system object"]
theorem tensorSystem_obj (I : Ideal A) (K : DerivedCategory (ModuleCat A)) (n : ℕ) :
    (tensorSystem I K).obj (op n) = (derivedTensorProduct K).obj (stage I n) := sorry

/-- The successor map formula after tensoring the ideal-power system with `K`. -/
@[simp, stacks 0922 "positive ideal-power derived tensor system transition"]
theorem tensorSystem_stepMap
    (I : Ideal A) (K : DerivedCategory (ModuleCat A)) (n : ℕ) :
    (tensorSystem I K).stepMap n = (derivedTensorProduct K).map (step I n) := sorry

end CategoryTheory.DerivedCategory.IdealPower
