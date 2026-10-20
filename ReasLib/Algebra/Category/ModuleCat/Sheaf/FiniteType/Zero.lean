module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteType
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Zero
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite type of zero module sheaves

The zero module sheaf is a reusable boundary case for finite-generation arguments, especially
when a direct image is extended by zero away from a closed subset.
-/

@[expose] public section

open CategoryTheory Limits
open scoped ZeroObject

noncomputable section

universe u v w

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{w}}
variable [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The zero sheaf of modules is of finite type. -/
@[stacks 01C4 "zero module sheaf"]
instance zero_isFiniteType :
    (0 : SheafOfModules.{w} R).IsFiniteType := sorry

/-- Any zero object in the category of module sheaves is of finite type. -/
@[stacks 01C4 "zero object"]
theorem IsFiniteType.of_isZero (M : SheafOfModules.{w} R) (hM : IsZero M) :
    M.IsFiniteType := sorry

variable (R)

#synth (0 : SheafOfModules.{w} R).IsFiniteType

end SheafOfModules
