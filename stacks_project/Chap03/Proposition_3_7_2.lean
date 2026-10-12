/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.SetTheory.Cardinal.Cofinality
import StacksCheckRecall

@[expose] public section

universe u

/- Proposition 3.7.2: for every cardinal `κ` there exists an ordinal whose cofinality is
strictly larger than `κ`. -/
@[stacks 05N3] #check
  (Cardinal.exists_ord_cof_gt : ∀ κ : Cardinal.{u}, ∃ o : Ordinal.{u}, κ < o.cof)
