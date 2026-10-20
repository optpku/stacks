/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

@[expose] public section

universe u

namespace FiniteField

/-- The arithmetic Frobenius of a finite field `k` is the `k`-algebra automorphism of
`AlgebraicClosure k` sending each `x` to `x ^ Fintype.card k`. -/
noncomputable def arithmeticFrobenius (k : Type u) [Field k] [Fintype k] :
    Gal(AlgebraicClosure k / k) :=
  frobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k)

end FiniteField
