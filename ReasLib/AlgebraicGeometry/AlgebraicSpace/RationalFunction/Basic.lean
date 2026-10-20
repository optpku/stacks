module

public import Mathlib.Algebra.Ring.MinimalAxioms
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RationalFunction.Operations

/-!
# The ring of rational functions on an algebraic space

The affine line `𝔸¹_S` is a ring object over `S`. Rational functions on an algebraic space
`X` over `S` are rational maps `X ⤏ 𝔸¹_S`, and they inherit addition and multiplication from
this ring-object structure.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TypeCat
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Addition of morphisms into the affine line. -/
instance instAddHomAffineLine {X : AlgebraicSpace S} : Add (X ⟶ affineLine S) where
  add := homAdd

/-- Multiplication of morphisms into the affine line. -/
instance instMulHomAffineLine {X : AlgebraicSpace S} : Mul (X ⟶ affineLine S) where
  mul := homMul

/-- Negation of morphisms into the affine line. -/
instance instNegHomAffineLine {X : AlgebraicSpace S} : Neg (X ⟶ affineLine S) where
  neg := homNeg

/-- The zero morphism into the affine line. -/
instance instZeroHomAffineLine {X : AlgebraicSpace S} : Zero (X ⟶ affineLine S) where
  zero := homZero X

/-- The unit morphism into the affine line. -/
instance instOneHomAffineLine {X : AlgebraicSpace S} : One (X ⟶ affineLine S) where
  one := homOne X

/-- Addition of morphisms into the affine line is associative. -/
theorem homAdd_assoc {X : AlgebraicSpace S} (f g h : X ⟶ affineLine S) :
    f + g + h = f + (g + h) :=
  sorry

/-- The zero morphism is a left identity for addition into the affine line. -/
theorem homZero_add {X : AlgebraicSpace S} (f : X ⟶ affineLine S) :
    0 + f = f :=
  sorry

/-- A morphism into the affine line added to its negative is zero. -/
theorem homNeg_add_cancel {X : AlgebraicSpace S} (f : X ⟶ affineLine S) :
    -f + f = 0 :=
  sorry

/-- Multiplication of morphisms into the affine line is associative. -/
theorem homMul_assoc {X : AlgebraicSpace S} (f g h : X ⟶ affineLine S) :
    f * g * h = f * (g * h) :=
  sorry

/-- Multiplication of morphisms into the affine line is commutative. -/
theorem homMul_comm {X : AlgebraicSpace S} (f g : X ⟶ affineLine S) :
    f * g = g * f :=
  sorry

/-- The unit morphism is a left identity for multiplication into the affine line. -/
theorem homOne_mul {X : AlgebraicSpace S} (f : X ⟶ affineLine S) :
    1 * f = f :=
  sorry

/-- Multiplication of morphisms into the affine line distributes over addition. -/
theorem homMul_add {X : AlgebraicSpace S} (f g h : X ⟶ affineLine S) :
    f * (g + h) = f * g + f * h :=
  sorry

/-- Morphisms from an algebraic space to the affine line form a commutative ring, with operations
induced by the ring-object structure of `𝔸¹_S`. -/
instance instCommRingHomAffineLine {X : AlgebraicSpace S} : CommRing (X ⟶ affineLine S) :=
  CommRing.ofMinimalAxioms homAdd_assoc homZero_add homNeg_add_cancel homMul_assoc
    homMul_comm homOne_mul homMul_add

/-- Addition on the rational-function quotient. -/
instance instAddRationalFunction {X : AlgebraicSpace S} : Add (RationalFunction X) where
  add := RationalFunction.add

/-- Multiplication on the rational-function quotient. -/
instance instMulRationalFunction {X : AlgebraicSpace S} : Mul (RationalFunction X) where
  mul := RationalFunction.mul

/-- Negation on the rational-function quotient. -/
instance instNegRationalFunction {X : AlgebraicSpace S} : Neg (RationalFunction X) where
  neg := RationalFunction.neg

/-- The zero element of the rational-function quotient. -/
instance instZeroRationalFunction {X : AlgebraicSpace S} : Zero (RationalFunction X) where
  zero := RationalFunction.zero

/-- The unit element of the rational-function quotient. -/
instance instOneRationalFunction {X : AlgebraicSpace S} : One (RationalFunction X) where
  one := RationalFunction.one

/-- Addition of rational functions is associative. -/
theorem RationalFunction.add_assoc {X : AlgebraicSpace S} (f g h : RationalFunction X) :
    f + g + h = f + (g + h) :=
  sorry

/-- The zero rational function is a left identity for addition. -/
theorem RationalFunction.zero_add {X : AlgebraicSpace S} (f : RationalFunction X) :
    0 + f = f :=
  sorry

/-- A rational function added to its negative is zero. -/
theorem RationalFunction.neg_add_cancel {X : AlgebraicSpace S} (f : RationalFunction X) :
    -f + f = 0 :=
  sorry

/-- Multiplication of rational functions is associative. -/
theorem RationalFunction.mul_assoc {X : AlgebraicSpace S} (f g h : RationalFunction X) :
    f * g * h = f * (g * h) :=
  sorry

/-- Multiplication of rational functions is commutative. -/
theorem RationalFunction.mul_comm {X : AlgebraicSpace S} (f g : RationalFunction X) :
    f * g = g * f :=
  sorry

/-- The unit rational function is a left identity for multiplication. -/
theorem RationalFunction.one_mul {X : AlgebraicSpace S} (f : RationalFunction X) :
    1 * f = f :=
  sorry

/-- Multiplication of rational functions distributes over addition. -/
theorem RationalFunction.left_distrib {X : AlgebraicSpace S} (f g h : RationalFunction X) :
    f * (g + h) = f * g + f * h :=
  sorry

/-- Rational functions on an algebraic space form a commutative ring, with addition and
multiplication induced by the ring-object structure of `𝔸¹_S`. -/
instance instCommRingRationalFunction {X : AlgebraicSpace S} : CommRing (RationalFunction X) :=
  CommRing.ofMinimalAxioms RationalFunction.add_assoc RationalFunction.zero_add
    RationalFunction.neg_add_cancel RationalFunction.mul_assoc RationalFunction.mul_comm
    RationalFunction.one_mul RationalFunction.left_distrib

/-- The ring of rational functions on an algebraic space `X`. -/
abbrev rationalFunctionRing (X : AlgebraicSpace S) : CommRingCat.{u + 1} :=
  CommRingCat.of (RationalFunction X)

/-- The ring of rational functions is the commutative ring of rational maps to the affine line. -/
theorem rationalFunctionRing_def (X : AlgebraicSpace S) :
    rationalFunctionRing X = CommRingCat.of (RationalFunction X) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
