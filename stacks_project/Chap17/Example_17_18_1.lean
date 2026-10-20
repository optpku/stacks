/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FiniteFreeRetract.Duality
import StacksCheckRecall

/-!
# Example 17.18.1

The example is the module-sheaf specialization of a general closed-monoidal duality
construction.  ReasLib owns the comparison morphism, the geometric invertibility criterion,
and the resulting exact pairing; this chapter file only records that reusable chain.
-/

@[expose] public section

open CategoryTheory

/- Example 17.18.1: the canonical map
`M ⊗ (ihom M).obj (𝟙_ C) ⟶ (ihom M).obj M` is defined in every braided closed
monoidal category. -/
@[stacks 0FNV "tensor-to-endomorphism comparison"]
#check @MonoidalClosed.tensorIhomUnitToEnd

#check @MonoidalClosed.tensorIhomUnitToEndInv
#check @MonoidalClosed.tensorIhomUnitToEnd_hom_inv_id
#check @MonoidalClosed.tensorIhomUnitToEnd_inv_hom_id
#check @MonoidalClosed.tensorIhomUnitToEndIso
#check @MonoidalClosed.tensorIhomUnitToEndIso_hom
#check @MonoidalClosed.tensorIhomUnitToEndIso_inv

/- Example 17.18.1: for module sheaves locally retracting from finite free modules, the
canonical tensor-to-endomorphism comparison is invertible. -/
@[stacks 0FNV "local finite-free retract criterion"]
#check @SheafOfModules.RingedSite.FiniteFreeRetract.IsLocal.isIso_tensorIhomUnitToEnd

/- Example 17.18.1: invertibility of the comparison canonically makes the internal Hom into the
tensor unit a left dual. -/
@[stacks 0FNV "canonical left dual"]
#check @MonoidalClosed.ihomUnitExactPairing
