/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.RingTheory.Localization.Away.ProdInt
import StacksCheckRecall

/- Exercise 111.7.5: with `A = ℤ × ℤ`, `I = Localization.ProdInt.ideal`, and
`S = Localization.ProdInt.submonoid`, the quotient and localization are related as follows. -/
@[stacks 076B] #check
  (Localization.ProdInt.algEquiv :
    ((ℤ × ℤ) ⧸ Localization.ProdInt.ideal) ≃ₐ[ℤ × ℤ]
      Localization.Away Localization.ProdInt.idempotent)

#check (Localization.ProdInt.ideal_ne_bot : Localization.ProdInt.ideal ≠ ⊥)
#check (Localization.ProdInt.ideal_ne_top : Localization.ProdInt.ideal ≠ ⊤)
