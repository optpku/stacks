module

public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Retract

/-!
# Finite coproducts of finite-free retract module sheaves

Retracts of finite free module sheaves contain a zero object and are stable under finite
coproducts.  These are module-level facts, independent of any complex or perfectness notion.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v w

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
variable {R : Sheaf J RingCat.{w}}

/-- The finite-free retract property contains a zero module sheaf. -/
instance finiteFreeRetractModuleProperty_containsZero :
    (finiteFreeRetractModuleProperty R).ContainsZero := sorry

/-- The finite-free retract property is stable under finite coproducts. -/
instance finiteFreeRetractModuleProperty_isClosedUnderFiniteCoproducts :
    (finiteFreeRetractModuleProperty R).IsClosedUnderFiniteCoproducts := sorry

/-- A binary coproduct of finite-free retract module sheaves is a finite-free retract. -/
theorem finiteFreeRetractModuleProperty_coprod {M N : SheafOfModules.{w} R}
    [HasBinaryCoproduct M N] (hM : finiteFreeRetractModuleProperty R M)
    (hN : finiteFreeRetractModuleProperty R N) :
    finiteFreeRetractModuleProperty R (M ⨿ N) := sorry

/-- A binary biproduct of finite-free retract module sheaves is a finite-free retract. -/
theorem finiteFreeRetractModuleProperty_biprod {M N : SheafOfModules.{w} R}
    [HasBinaryBiproduct M N] (hM : finiteFreeRetractModuleProperty R M)
    (hN : finiteFreeRetractModuleProperty R N) :
    finiteFreeRetractModuleProperty R (M ⊞ N) := sorry

end SheafOfModules
