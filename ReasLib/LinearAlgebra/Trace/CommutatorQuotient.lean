/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Trace
public import ReasLib.Algebra.Ring.CommutatorQuotient

/-!
# Trace of a free left module into the commutator quotient

The additive traces `Matrix.traceNatural` and `LinearMap.traceNatural`
take values in `R♮`. Endomorphisms of the standard free left module
are represented by right matrix action `a(v) = v ᵥ* A`.
-/

@[expose] public section

universe u v

open Ring

namespace Matrix

variable (n : Type v) (R : Type u) [Fintype n] [NonUnitalNonAssocRing R]

/-- The trace of a square matrix, as an additive map into the commutator quotient. -/
def traceNatural : Matrix n n R →+ CommutatorQuotient R :=
  CommutatorQuotient.mk.comp (traceAddMonoidHom n R)

/-- The matrix trace in the commutator quotient is the class of the diagonal sum. -/
theorem traceNatural_apply (A : Matrix n n R) :
    traceNatural n R A = CommutatorQuotient.mk (trace A) := sorry

/-- The traces of the two products of rectangular matrices agree in the additive
commutator quotient, without assuming commutativity of the coefficient ring. -/
theorem traceNatural_mul_comm {m n : Type v} {R : Type u}
    [Fintype m] [Fintype n] [NonUnitalNonAssocRing R]
    (A : Matrix m n R) (B : Matrix n m R) :
    traceNatural m R (A * B) = traceNatural n R (B * A) := sorry

end Matrix

namespace LinearMap

variable {R : Type u} [Ring R] {n : Type v} [Fintype n] [DecidableEq n]

/-- The trace of a left-linear endomorphism of the standard free module `n → R`,
as the class of the diagonal sum of its right-acting matrix. -/
def traceNatural : Module.End R (n → R) →+ CommutatorQuotient R :=
  (Matrix.traceNatural n R).comp toMatrixRight'.toLinearMap.toAddMonoidHom

/-- The free-module trace is the class of the diagonal sum of the right-acting matrix. -/
theorem traceNatural_apply (f : Module.End R (n → R)) :
    traceNatural f = CommutatorQuotient.mk (Matrix.trace f.toMatrixRight') := sorry

/-- The free-module trace is the matrix trace of the right-acting representing matrix. -/
theorem traceNatural_toMatrixRight' (f : Module.End R (n → R)) :
    traceNatural f = Matrix.traceNatural n R f.toMatrixRight' := sorry

/-- For left-linear maps between standard finite free modules in opposite
directions, the traces of their composites agree in the additive commutator quotient. -/
theorem traceNatural_comp_comm {R : Type u} [Ring R] {m n : Type v}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (a : (m → R) →ₗ[R] (n → R)) (b : (n → R) →ₗ[R] (m → R)) :
    traceNatural (a ∘ₗ b) = traceNatural (b ∘ₗ a) := sorry

end LinearMap
