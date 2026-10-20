module

import StacksCheckRecall
import ReasLib.SetTheory.Reflection

@[expose] public section

universe u

noncomputable section

open FirstOrder Order
open scoped ZFSet

/- Theorem 3.8.1. Given a finite family of formulas of set theory and a set `M0`, there is a
limit level `V_ o` containing `M0` that reflects their simultaneous satisfaction. -/
@[stacks 000G] #check (ZFSet.exists_vonNeumann_reflects :
  ∀ {n m : ℕ} (φ : Fin m → Language.setTheory.Formula (Fin n)) (M0 : ZFSet.{u}),
    ∃ o : Ordinal.{u}, IsSuccLimit o ∧ M0 ⊆ V_ o ∧
      ZFSet.Reflects (V_ o) (Language.Formula.iInf φ))
