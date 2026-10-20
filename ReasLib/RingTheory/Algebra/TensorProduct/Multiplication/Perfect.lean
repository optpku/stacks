module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Algebra.TensorProduct.Multiplication
public import ReasLib.RingTheory.RingHom.Perfect.Basic
public import ReasLib.RingTheory.RingHom.Perfect.TorDimension

/-!
# Perfect tensor-square multiplication

This is the intrinsic, presentation-theoretic form of perfectness for the
diagonal map.  Unlike a chosen derived-module model, it is universe-polymorphic.
-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace RingHom

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- The map-first perfect-diagonal condition used in Lemmas 23.10.1 (0FCW) and 23.10.2
(0FCX). -/
@[algebraize RingHom.DiagonalIsPerfect.toAlgebra,
  stacks 0FCW "perfect diagonal of a ring map",
  stacks 0FCX "perfect diagonal of a ring map"]
def DiagonalIsPerfect (f : A →+* B) : Prop :=
  (@Algebra.tensorSquareMultiplication A B _ _ f.toAlgebra).IsPerfectRingMap

/-- Finite Tor dimension of tensor-square multiplication, stated intrinsically for a ring map. -/
@[algebraize RingHom.DiagonalHasFiniteTorDimension.toAlgebra,
  stacks 0FCW "finite Tor dimension of the diagonal",
  stacks 0FCX "finite Tor dimension of the diagonal"]
def DiagonalHasFiniteTorDimension (f : A →+* B) : Prop :=
  (@Algebra.tensorSquareMultiplication A B _ _ f.toAlgebra).HasFiniteTorDimension

/-- The map-first perfect-diagonal predicate specializes to tensor-square multiplication for an
ambient algebra. -/
theorem diagonalIsPerfect_algebraMap
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] :
    (algebraMap A B).DiagonalIsPerfect ↔
      (Algebra.tensorSquareMultiplication A B).IsPerfectRingMap := sorry

/-- The map-first finite-Tor diagonal predicate specializes to tensor-square multiplication for an
ambient algebra. -/
theorem diagonalHasFiniteTorDimension_algebraMap
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B] :
    (algebraMap A B).DiagonalHasFiniteTorDimension ↔
      (Algebra.tensorSquareMultiplication A B).HasFiniteTorDimension := sorry

namespace DiagonalIsPerfect

/-- The algebra structure induced by a map with perfect diagonal has perfect tensor-square
multiplication. -/
theorem toAlgebra {f : A →+* B} (hf : f.DiagonalIsPerfect) :
    (@Algebra.tensorSquareMultiplication A B _ _ f.toAlgebra).IsPerfectRingMap := sorry

/-- A perfect diagonal has finite Tor dimension. -/
theorem hasFiniteTorDimension {f : A →+* B} (hf : f.DiagonalIsPerfect) :
    f.DiagonalHasFiniteTorDimension := sorry

end DiagonalIsPerfect

namespace DiagonalHasFiniteTorDimension

/-- The algebra structure induced by a map whose diagonal has finite Tor dimension has the same
property for tensor-square multiplication. -/
theorem toAlgebra {f : A →+* B} (hf : f.DiagonalHasFiniteTorDimension) :
    (@Algebra.tensorSquareMultiplication A B _ _ f.toAlgebra).HasFiniteTorDimension := sorry

end DiagonalHasFiniteTorDimension

end RingHom
