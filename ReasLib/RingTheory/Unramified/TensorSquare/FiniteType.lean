/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Unramified.TensorSquare
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite-type unramifiedness from a flat diagonal

This leaf records the finite-type corollary of the tensor-square criterion.  The
formal-unramified core remains owned by the parent `TensorSquare` module.

@stack 0CKP
-/

@[expose] public section

universe u v

namespace Algebra.Unramified

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

/-- A finite-type algebra with flat tensor-square multiplication is unramified. -/
@[stacks 0CKP "finite-type flat diagonal criterion for unramifiedness"]
theorem of_tensorSquareMul_flat [Algebra.FiniteType A B]
    (hflat : (Algebra.tensorSquareMultiplication A B).Flat) :
    Algebra.Unramified A B := by
  letI : Algebra.FormallyUnramified A B :=
    Algebra.FormallyUnramified.of_tensorSquareMul_flat hflat
  exact { formallyUnramified := inferInstance, finiteType := inferInstance }

end Algebra.Unramified
