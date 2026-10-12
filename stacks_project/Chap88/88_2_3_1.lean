/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap88.«88_2_3_1_BaseChange»
import StacksCheckRecall

@[expose] public section

/- 88.2.3.1: given a ring map `φ : A₁ →+* A₂` and ideals `Iᵢ` with
`φ(I₁ ^ c) ⊆ I₂` for some `c ≥ 1`, there is a base-change functor
`C₁ ⥤ C₂` sending `(B n)` to
`B (c * n) ⊗[A₁ ⧸ I₁ ^ (c * n)] (A₂ ⧸ I₂ ^ n)`. -/
@[stacks 0AJZ] #check AdicAlgebraSystem.baseChange
