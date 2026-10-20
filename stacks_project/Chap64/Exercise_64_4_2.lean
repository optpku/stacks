/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap64.Definition_64_4_1_Trace
import StacksCheckRecall

@[expose] public section

universe u v

/- Exercise 64.4.2: given left-linear maps `a : (m → R) →ₗ[R] (n → R)` and
`b : (n → R) →ₗ[R] (m → R)` of standard free left modules, corresponding to
source maps `a : Λ^⊕m ⟶ Λ^⊕n` and `b : Λ^⊕n ⟶ Λ^⊕m`, the traces of the
composites agree in the commutator quotient: `Tr(ab) = Tr(ba)` as
`LinearMap.traceNatural (a ∘ₗ b) = LinearMap.traceNatural (b ∘ₗ a)`. -/
@[stacks 03T1] #check (LinearMap.traceNatural_comp_comm :
  ∀ {R : Type u} [Ring R] {m n : Type v}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (a : (m → R) →ₗ[R] (n → R)) (b : (n → R) →ₗ[R] (m → R)),
    LinearMap.traceNatural (a ∘ₗ b) = LinearMap.traceNatural (b ∘ₗ a))

#check (Matrix.traceNatural_mul_comm :
  ∀ {m n : Type v} {R : Type u} [Fintype m] [Fintype n] [NonUnitalNonAssocRing R]
    (A : Matrix m n R) (B : Matrix n m R),
    Matrix.traceNatural m R (A * B) = Matrix.traceNatural n R (B * A))
