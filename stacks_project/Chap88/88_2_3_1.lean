module

public import stacks_project.Chap88.«88_2_3_1_BaseChange»
import StacksCheckRecall

@[expose] public section

/- 88.2.3.1: given a ring map `φ : A₁ →+* A₂` and ideals `Iᵢ` with
`φ(I₁ ^ c) ⊆ I₂` for some `c ≥ 1`, there is a base-change functor
`C₁ ⥤ C₂` sending `(B n)` to
`B (c * n) ⊗[A₁ ⧸ I₁ ^ (c * n)] (A₂ ⧸ I₂ ^ n)`. -/
@[stacks 0AJZ] #check AdicAlgebraSystem.baseChange
