/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra

/-!
# Commutative differential graded algebras

This leaf adds the Koszul-sign commutativity and strict commutativity predicates
to the elementary chain and cochain differential graded algebra structures.
-/

@[expose] public section

universe u v

variable {R : Type u} [CommRing R]

namespace ChainDGAlgebra

/-- Definition 22.3.3 (1): a chain differential graded algebra is commutative when swapping
homogeneous factors of degrees `n` and `m` introduces the Koszul sign `(-1)^(n * m)`. -/
@[stacks 061W, mk_iff isCommutative_iff]
class IsCommutative (A : ChainDGAlgebra.{u, v} R) : Prop where
  /-- Swapping two homogeneous factors introduces the Koszul sign. -/
  mul_comm {n m : ℤ} (a : A.X n) (b : A.X m) :
      A.mul n m a b =
        cast (congrArg (fun i : ℤ ↦ (A.X i : Type v)) (add_comm m n))
          (((n * m).negOnePow : R) • A.mul m n b a)

/-- In a commutative chain differential graded algebra, swapping homogeneous factors obeys the
Koszul sign rule. -/
theorem mul_comm_apply (A : ChainDGAlgebra.{u, v} R) [h : A.IsCommutative]
    {n m : ℤ} (a : A.X n) (b : A.X m) :
    A.mul n m a b =
      cast (congrArg (fun i : ℤ ↦ (A.X i : Type v)) (add_comm m n))
        (((n * m).negOnePow : R) • A.mul m n b a) := sorry

/-- Definition 22.3.3 (2): a chain differential graded algebra is strictly commutative when it
is graded commutative and every odd-degree homogeneous element has square zero. -/
@[stacks 061W, mk_iff isStrictlyCommutative_iff]
class IsStrictlyCommutative (A : ChainDGAlgebra.{u, v} R) extends IsCommutative A where
  /-- Odd-degree homogeneous elements square to zero. -/
  sq_eq_zero_of_odd {n : ℤ} (hn : Odd n) (a : A.X n) : A.mul n n a a = 0

/-- In a strictly commutative chain differential graded algebra, an odd-degree homogeneous
element squares to zero. -/
theorem mul_self_eq_zero_of_odd (A : ChainDGAlgebra.{u, v} R) [h : A.IsStrictlyCommutative]
    {n : ℤ} (hn : Odd n) (a : A.X n) :
    A.mul n n a a = 0 := sorry

end ChainDGAlgebra

namespace CochainDGAlgebra

/-- Definition 22.3.3 (1): a cochain differential graded algebra is commutative when swapping
homogeneous factors of degrees `n` and `m` introduces the Koszul sign `(-1)^(n * m)`. -/
@[stacks 061W, mk_iff isCommutative_iff]
class IsCommutative (A : CochainDGAlgebra.{u, v} R) : Prop where
  /-- Swapping two homogeneous factors introduces the Koszul sign. -/
  mul_comm {n m : ℤ} (a : A.X n) (b : A.X m) :
      A.mul n m a b =
        cast (congrArg (fun i : ℤ ↦ (A.X i : Type v)) (add_comm m n))
          (((n * m).negOnePow : R) • A.mul m n b a)

/-- In a commutative cochain differential graded algebra, swapping homogeneous factors obeys
the Koszul sign rule. -/
theorem mul_comm_apply (A : CochainDGAlgebra.{u, v} R) [h : A.IsCommutative]
    {n m : ℤ} (a : A.X n) (b : A.X m) :
    A.mul n m a b =
      cast (congrArg (fun i : ℤ ↦ (A.X i : Type v)) (add_comm m n))
        (((n * m).negOnePow : R) • A.mul m n b a) := sorry

/-- Definition 22.3.3 (2): a cochain differential graded algebra is strictly commutative when
it is graded-commutative and every odd-degree homogeneous element has square zero. -/
@[stacks 061W, mk_iff isStrictlyCommutative_iff]
class IsStrictlyCommutative (A : CochainDGAlgebra.{u, v} R) extends IsCommutative A where
  /-- Odd-degree homogeneous elements square to zero. -/
  sq_eq_zero_of_odd {n : ℤ} (hn : Odd n) (a : A.X n) : A.mul n n a a = 0

/-- In a strictly commutative cochain differential graded algebra, an odd-degree homogeneous
element squares to zero. -/
theorem mul_self_eq_zero_of_odd (A : CochainDGAlgebra.{u, v} R) [h : A.IsStrictlyCommutative]
    {n : ℤ} (hn : Odd n) (a : A.X n) :
    A.mul n n a a = 0 := sorry

end CochainDGAlgebra
