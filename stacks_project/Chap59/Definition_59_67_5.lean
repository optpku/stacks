/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.Cr
import StacksCheckRecall

universe u

/- Definition 59.67.5: a field `K` is called `C_r` when every homogeneous
polynomial of degree `d` in `n` variables with `0 < d ^ r < n` has a
nontrivial solution in `K`. -/
@[stacks 03R9] #check (@Field.IsCr : (K : Type u) → Field K → ℕ → Prop)
