/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.LinearAlgebra.Matrix.PeriodicComplex
import StacksCheckRecall

@[expose] public section

universe u

/- Exercise 111.14.3: for a commutative ring `R`, `n ≥ 1`, and `n × n` matrices `A`, `B` with
`A * B = f • 1` for a nonzerodivisor `f`, the bi-infinite period-2 cochain complex of free
modules `Fin n → R ⧸ Ideal.span {f}` with even differentials induced by `B` and odd differentials
induced by `A` is acyclic. -/
@[stacks 0D1S] #check
  (Matrix.periodicCochain_acyclic : ∀ {R : Type u} [CommRing R] {n : ℕ} [NeZero n]
    (A B : Matrix (Fin n) (Fin n) R) {f : R}
    (hAB : A * B = f • 1) (hf : f ∈ nonZeroDivisors R),
    (Matrix.periodicCochain A B hAB hf).Acyclic)
