/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.Principal

/-!
# Weil divisor class groups of algebraic spaces

The Weil divisor class group of a locally Noetherian integral algebraic space is
the quotient of the group of Weil divisors by the subgroup of principal Weil
divisors. Notation: Cl(X).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} (X : AlgebraicSpace S)
variable [IsLocallyNoetherian X] [IsIntegral X]

/-- A Weil divisor is principal when it is the principal divisor of a rational
function. -/
def IsPrincipalWeilDivisor (D : WeilDivisor X) : Prop :=
  ∃ f : (RationalFunction X)ˣ, D = principalWeilDivisor X f

/-- Principality is equivalent to matching the order-of-vanishing coefficients of
some rational unit. -/
theorem IsPrincipalWeilDivisor_iff_coeff (D : WeilDivisor X) :
    IsPrincipalWeilDivisor X D ↔
      ∃ f : (RationalFunction X)ˣ,
        ∀ Z : PrimeDivisor X, D.coeff Z = Z.ord f :=
  sorry

/-- The zero Weil divisor is principal. -/
theorem IsPrincipalWeilDivisor.zero : IsPrincipalWeilDivisor X 0 :=
  sorry

/-- The sum of two principal Weil divisors is principal. -/
theorem IsPrincipalWeilDivisor.add {D E : WeilDivisor X}
    (hD : IsPrincipalWeilDivisor X D) (hE : IsPrincipalWeilDivisor X E) :
    IsPrincipalWeilDivisor X (D + E) :=
  sorry

/-- The negation of a principal Weil divisor is principal. -/
theorem IsPrincipalWeilDivisor.neg {D : WeilDivisor X}
    (hD : IsPrincipalWeilDivisor X D) : IsPrincipalWeilDivisor X (-D) :=
  sorry

/-- The subgroup of principal Weil divisors. -/
def principalWeilDivisors : AddSubgroup (WeilDivisor X) where
  carrier := IsPrincipalWeilDivisor X
  zero_mem' := IsPrincipalWeilDivisor.zero X
  add_mem' := IsPrincipalWeilDivisor.add X
  neg_mem' := IsPrincipalWeilDivisor.neg X

/-- The subgroup of principal Weil divisors on an algebraic space. -/
scoped notation "Prin(" X ")" => principalWeilDivisors X

/-- Membership in the principal-divisor subgroup is the principal-divisor
predicate. -/
theorem mem_principalWeilDivisors_iff (D : WeilDivisor X) :
    D ∈ principalWeilDivisors X ↔ IsPrincipalWeilDivisor X D :=
  Iff.rfl

/-- The principal Weil divisor of a rational function belongs to the principal
divisor subgroup. -/
theorem principalWeilDivisor_mem_principalWeilDivisors
    (f : (RationalFunction X)ˣ) :
    principalWeilDivisor X f ∈ principalWeilDivisors X :=
  ⟨f, rfl⟩

/-- The Weil divisor class group is the quotient of Weil divisors by principal
Weil divisors. -/
abbrev WeilDivisorClassGroup : Type (u + 1) :=
  WeilDivisor X ⧸ principalWeilDivisors X

/-- The Weil divisor class group of an algebraic space. -/
scoped notation "Cl(" X ")" => WeilDivisorClassGroup X

/-- The canonical quotient homomorphism from Weil divisors to the divisor class
group. -/
abbrev weilDivisorClassGroupMk : WeilDivisor X →+ WeilDivisorClassGroup X :=
  QuotientAddGroup.mk' (principalWeilDivisors X)

/-- The quotient map from Weil divisors to the class group is surjective. -/
theorem weilDivisorClassGroupMk_surjective :
    Function.Surjective (weilDivisorClassGroupMk X) :=
  QuotientAddGroup.mk'_surjective (principalWeilDivisors X)

/-- Two Weil divisors determine the same class if and only if their difference
is principal. -/
theorem weilDivisorClassGroupMk_eq_iff (D E : WeilDivisor X) :
    weilDivisorClassGroupMk X D = weilDivisorClassGroupMk X E ↔
      D - E ∈ principalWeilDivisors X :=
  sorry

/-- The principal-divisor map followed by the class-group quotient is a
right-exact presentation of the Weil divisor class group. -/
theorem weilDivisorClass_exactSequence :
    Function.Exact (principalWeilDivisor X) (weilDivisorClassGroupMk X) ∧
      Function.Surjective (weilDivisorClassGroupMk X) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
