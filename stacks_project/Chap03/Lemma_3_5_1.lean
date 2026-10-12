/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.SetTheory.ZFC.VonNeumann
import StacksCheckRecall

@[expose] public section

universe u

open scoped ZFSet

/- Lemma 3.5.1: every set `x : ZFSet` is an element of `V_ o` for some ordinal `o`. -/
@[stacks 000C] #check
  (ZFSet.exists_mem_vonNeumannLevel :
    ∀ x : ZFSet.{u}, ∃ ordinal : Ordinal.{u}, x ∈ V_ ordinal)
