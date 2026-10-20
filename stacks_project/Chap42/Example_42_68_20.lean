/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.NumberTheory.Padics.TameSymbol.ScalarQuotient
import StacksCheckRecall

@[expose] public section

noncomputable section

open scoped nonZeroDivisors Pointwise

variable (p : ℕ) [Fact p.Prime]
variable (l a b : ℕ) (h_ab : a + b = l) (u v : ℤ_[p]ˣ)

/- Example 42.68.20: for `a + b = l`, the periodic determinant of the scalar quotient
with differentials `p ^ b * u` and `p ^ a * v` is the reduction of
`(-1) ^ (a * b) * u ^ a / v ^ b` modulo `p`. -/
@[stacks 02PQ] #check
  (PadicInt.TwoPeriodic.scalarQuotientSelfDeterminant_primePowerUnits
    p l a b h_ab u v :
      Units.map PadicInt.residueField.toMonoidHom
          (CategoryTheory.TwoPeriodicEndomorphism.scalarQuotientSelfDeterminant
            ((p : ℤ_[p]) ^ b * (u : ℤ_[p])) ((p : ℤ_[p]) ^ a * (v : ℤ_[p]))
            (PadicInt.TwoPeriodic.primePowerUnit_mem_nonZeroDivisors p b u)
            (PadicInt.TwoPeriodic.primePowerUnit_mem_nonZeroDivisors p a v)
            (IsDiscreteValuationRing.ringKrullDim_eq_one ℤ_[p])) =
        Units.map PadicInt.toZMod.toMonoidHom
          ((-1 : ℤ_[p]ˣ) ^ (a * b) * u ^ a / v ^ b))

#check
  (PadicInt.TwoPeriodic.primePowerUnits_smulTop_eq p l a b h_ab u v :
    (((p : ℤ_[p]) ^ b * (u : ℤ_[p])) * ((p : ℤ_[p]) ^ a * (v : ℤ_[p]))) •
        (⊤ : Submodule ℤ_[p] ℤ_[p]) =
      (p : ℤ_[p]) ^ l • (⊤ : Submodule ℤ_[p] ℤ_[p]))

#check
  (PadicInt.TwoPeriodic.unitFormula_eq_tameSymbol p a b u v :
    Units.map PadicInt.toZMod.toMonoidHom
        ((-1 : ℤ_[p]ˣ) ^ (a * b) * u ^ a / v ^ b) =
      Units.map PadicInt.residueField.toMonoidHom
        (DVR.TameSymbol.value ℤ_[p] ℚ_[p]
          (DVR.TameSymbol.mapNonzero ℤ_[p] ℚ_[p]
            (PadicInt.TwoPeriodic.primePowerNonzeroDivisor p b u))
          (DVR.TameSymbol.mapNonzero ℤ_[p] ℚ_[p]
            (PadicInt.TwoPeriodic.primePowerNonzeroDivisor p a v))))
