/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.CentralSimple.BrauerGroup.Cr
import StacksCheckRecall

universe u

/- Theorem 59.67.8: if `K` is a `C₁` field, every Brauer class over `K` is the neutral class. -/
@[stacks 03RC] #check (BrauerGroup.eq_one_of_isCr : ∀ {K : Type u} [Field K]
  (hC1 : Field.IsCr K 1) (A : Br(K)), A = 1)
