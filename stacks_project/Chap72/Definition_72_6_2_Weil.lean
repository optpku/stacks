module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Topology.LocallyFinite
public import stacks_project.Chap72.Definition_72_6_2_Prime

/-!
# Weil divisors on algebraic spaces

A Weil divisor is a locally finite integer linear combination of prime
divisors.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]

/-- A Weil divisor is a formal integer linear combination of prime divisors
whose nonzero-coefficient supports form a locally finite family in `Points X`. -/
def WeilDivisor :=
  { coeff : PrimeDivisor X → ℤ //
    LocallyFinite fun Z : PrimeDivisor X ↦
      if coeff Z = 0 then (∅ : Set (Points X)) else Z.pointsSet }

/-- Construct a Weil divisor from an integer coefficient function whose nonzero
support family is locally finite. -/
def WeilDivisor.ofCoeff (coeff : PrimeDivisor X → ℤ)
    (locallyFinite_support : LocallyFinite fun Z : PrimeDivisor X ↦
      if coeff Z = 0 then (∅ : Set (Points X)) else Z.pointsSet) :
    WeilDivisor X :=
  ⟨coeff, locallyFinite_support⟩

/-- The integer coefficient of a prime divisor in a Weil divisor. -/
abbrev WeilDivisor.coeff {Y : AlgebraicSpace S} [IsDecent Y] (D : WeilDivisor Y) :
    PrimeDivisor Y → ℤ :=
  D.1

/-- Coefficients recovered from `ofCoeff` are the original function. -/
theorem WeilDivisor.coeff_ofCoeff (coeff : PrimeDivisor X → ℤ)
    (locallyFinite_support : LocallyFinite fun Z : PrimeDivisor X ↦
      if coeff Z = 0 then (∅ : Set (Points X)) else Z.pointsSet)
    (Z : PrimeDivisor X) :
    (ofCoeff X coeff locallyFinite_support).coeff Z = coeff Z :=
  sorry

/-- The family attached to a Weil divisor, supported on those prime divisors
with nonzero coefficient. -/
abbrev WeilDivisor.supportFamily {Y : AlgebraicSpace S} [IsDecent Y] (D : WeilDivisor Y) :
    PrimeDivisor Y → Set (Points Y) := fun Z ↦
  if D.coeff Z = 0 then (∅ : Set (Points Y)) else Z.pointsSet

/-- The nonzero-coefficient support family of a Weil divisor is locally finite. -/
theorem WeilDivisor.locallyFinite_supportFamily {Y : AlgebraicSpace S} [IsDecent Y]
    (D : WeilDivisor Y) :
    LocallyFinite D.supportFamily :=
  sorry

/-- The zero coefficient function has locally finite nonzero support. -/
theorem WeilDivisor.locallyFinite_supportFamily_zero :
    LocallyFinite fun Z : PrimeDivisor X ↦
      if (fun _ : PrimeDivisor X ↦ (0 : ℤ)) Z = 0 then (∅ : Set (Points X))
      else Z.pointsSet :=
  sorry

/-- The coefficientwise sum of two Weil divisors has locally finite nonzero
support. -/
theorem WeilDivisor.locallyFinite_supportFamily_add (D E : WeilDivisor X) :
    LocallyFinite fun Z : PrimeDivisor X ↦
      if D.coeff Z + E.coeff Z = 0 then (∅ : Set (Points X)) else Z.pointsSet :=
  sorry

/-- The coefficientwise negation of a Weil divisor has locally finite nonzero
support. -/
theorem WeilDivisor.locallyFinite_supportFamily_neg (D : WeilDivisor X) :
    LocallyFinite fun Z : PrimeDivisor X ↦
      if -D.coeff Z = 0 then (∅ : Set (Points X)) else Z.pointsSet :=
  sorry

/-- The coefficientwise difference of two Weil divisors has locally finite
nonzero support. -/
theorem WeilDivisor.locallyFinite_supportFamily_sub (D E : WeilDivisor X) :
    LocallyFinite fun Z : PrimeDivisor X ↦
      if D.coeff Z - E.coeff Z = 0 then (∅ : Set (Points X)) else Z.pointsSet :=
  sorry

/-- Two Weil divisors with equal coefficients are equal. -/
theorem WeilDivisor.ext {D E : WeilDivisor X}
    (hcoeff : ∀ Z : PrimeDivisor X, D.coeff Z = E.coeff Z) : D = E :=
  sorry

/-- The zero Weil divisor has all coefficients equal to `0`. -/
instance instZeroWeilDivisor : Zero (WeilDivisor X) where
  zero := WeilDivisor.ofCoeff X (fun _ ↦ 0) (WeilDivisor.locallyFinite_supportFamily_zero X)

/-- Addition of Weil divisors is defined coefficientwise. -/
instance instAddWeilDivisor : Add (WeilDivisor X) where
  add D E :=
    WeilDivisor.ofCoeff X (fun Z ↦ D.coeff Z + E.coeff Z)
      (WeilDivisor.locallyFinite_supportFamily_add X D E)

/-- Negation of Weil divisors is defined coefficientwise. -/
instance instNegWeilDivisor : Neg (WeilDivisor X) where
  neg D :=
    WeilDivisor.ofCoeff X (fun Z ↦ -D.coeff Z)
      (WeilDivisor.locallyFinite_supportFamily_neg X D)

/-- Subtraction of Weil divisors is defined coefficientwise. -/
instance instSubWeilDivisor : Sub (WeilDivisor X) where
  sub D E :=
    WeilDivisor.ofCoeff X (fun Z ↦ D.coeff Z - E.coeff Z)
      (WeilDivisor.locallyFinite_supportFamily_sub X D E)

/-- Every coefficient of the zero Weil divisor is zero. -/
theorem WeilDivisor.coeff_zero (Z : PrimeDivisor X) : (0 : WeilDivisor X).coeff Z = 0 :=
  sorry

/-- The coefficient of a sum of Weil divisors is the sum of their coefficients. -/
theorem WeilDivisor.coeff_add (D E : WeilDivisor X) (Z : PrimeDivisor X) :
    (D + E).coeff Z = D.coeff Z + E.coeff Z :=
  sorry

/-- The coefficient of the negation of a Weil divisor is the negation of its
coefficient. -/
theorem WeilDivisor.coeff_neg (D : WeilDivisor X) (Z : PrimeDivisor X) :
    (-D).coeff Z = -D.coeff Z :=
  sorry

/-- The coefficient of a difference of Weil divisors is the difference of their
coefficients. -/
theorem WeilDivisor.coeff_sub (D E : WeilDivisor X) (Z : PrimeDivisor X) :
    (D - E).coeff Z = D.coeff Z - E.coeff Z :=
  sorry

/-- Weil divisors form an additive commutative group under pointwise operations
on coefficients. -/
instance instAddCommGroupWeilDivisor : AddCommGroup (WeilDivisor X) where
  add := Add.add
  zero := Zero.zero
  neg := Neg.neg
  sub := Sub.sub
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := sorry
  zero_add := sorry
  add_zero := sorry
  add_comm := sorry
  neg_add_cancel := sorry
  nsmul_zero := sorry
  nsmul_succ := sorry
  sub_eq_add_neg := sorry
  zsmul_zero' := sorry
  zsmul_succ' := sorry
  zsmul_neg' := sorry

/-- The group of Weil divisors on an algebraic space. -/
scoped notation "Div(" X ")" => WeilDivisor X

end AlgebraicGeometry.AlgebraicSpace
