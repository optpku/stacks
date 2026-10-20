/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Algebra
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Commutativity predicates for graded algebra sheaves

This leaf distinguishes ordinary commutativity for algebra sheaves graded by a commutative
additive monoid from the Koszul sign rule for algebra sheaves graded by natural numbers. Both
predicates are independent of particular constructions such as exterior or symmetric powers.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.GradedAlgebraSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- An algebra sheaf graded by a commutative additive monoid is ordinarily commutative when
homogeneous local sections commute without a sign. -/
@[stacks 01CF "commutative graded algebra sheaves"]
class IsCommutative {ι : Type} [AddCommMonoid ι]
    (A : GradedAlgebraSheaf 𝒪 ι) : Prop where
  /-- Ordinary commutativity for homogeneous local sections. -/
  mul_comm : ∀ (U : Cᵒᵖ) (n m : ι)
    (a : A.sections U n) (b : A.sections U m),
    HEq (A.mul U n m a b) (A.mul U m n b a)

/-- Homogeneous local sections of an ordinarily commutative graded algebra sheaf commute without
a sign. -/
theorem mul_comm_of_isCommutative
    {ι : Type} [AddCommMonoid ι] (A : GradedAlgebraSheaf 𝒪 ι) [A.IsCommutative]
    (U : Cᵒᵖ) (n m : ι) (a : A.sections U n) (b : A.sections U m) :
    HEq (A.mul U n m a b) (A.mul U m n b a) := sorry

/-- A naturally graded algebra sheaf is graded commutative when swapping homogeneous local
sections of degrees `n` and `m` contributes the Koszul sign `(-1)^(n * m)`. -/
@[stacks 01CF "graded-commutative algebra sheaves"]
class IsGradedCommutative (A : GradedAlgebraSheaf 𝒪 ℕ) : Prop where
  /-- The Koszul sign rule for homogeneous local sections. -/
  mul_comm : ∀ (U : Cᵒᵖ) (n m : ℕ)
    (a : A.sections U n) (b : A.sections U m),
    HEq (A.mul U n m a b)
      ((-1 : 𝒪.obj.obj U) ^ (n * m) • A.mul U m n b a)

/-- Homogeneous local sections of a graded-commutative algebra sheaf satisfy the Koszul sign
rule. -/
theorem mul_comm
    (A : GradedAlgebraSheaf 𝒪 ℕ) [A.IsGradedCommutative]
    (U : Cᵒᵖ) (n m : ℕ) (a : A.sections U n) (b : A.sections U m) :
    HEq (A.mul U n m a b)
      ((-1 : 𝒪.obj.obj U) ^ (n * m) • A.mul U m n b a) := sorry

end SheafOfModules.RingedSite.GradedAlgebraSheaf
