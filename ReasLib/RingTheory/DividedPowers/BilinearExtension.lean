/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Ring.MinimalAxioms
public import Mathlib.RingTheory.DividedPowers.DPMorphism

@[expose] public section

universe u v w

namespace DividedPowers

/-- The explicit triple carrier for a bilinear second-order extension. -/
def BilinearExtension (A : Type u) (M : Type v) (N : Type w)
    [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (q : M →ₗ[A] M →ₗ[A] N) := A × M × N

namespace BilinearExtension

variable {A : Type u} {M : Type v} {N : Type w}
variable [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
variable (q : M →ₗ[A] M →ₗ[A] N)

/-- The canonical element of the extension represented by an explicit triple. -/
def ofTriple (x : A × M × N) : BilinearExtension A M N q := x

/-- The underlying triple of an element of the bilinear extension. -/
def toTriple (a : BilinearExtension A M N q) : A × M × N := a

/-- Converting an explicit triple to the extension and back is the identity. -/
theorem toTriple_ofTriple (x : A × M × N) : toTriple q (ofTriple q x) = x := sorry

/-- Every element of the extension is determined by its underlying triple. -/
theorem ofTriple_toTriple (a : BilinearExtension A M N q) :
    ofTriple q (toTriple q a) = a := sorry

/-- Addition on the explicit triple carrier. -/
instance instAdd : Add (BilinearExtension A M N q) where
  add a b := ofTriple q (toTriple q a + toTriple q b)

/-- Zero on the explicit triple carrier. -/
instance instZero : Zero (BilinearExtension A M N q) where
  zero := ofTriple q 0

/-- Negation on the explicit triple carrier. -/
instance instNeg : Neg (BilinearExtension A M N q) where
  neg a := ofTriple q (-toTriple q a)

/-- Scalar multiplication on the explicit triple carrier. -/
instance instSMul : SMul A (BilinearExtension A M N q) where
  smul a x := ofTriple q (a • toTriple q x)

/-- The displayed symmetrized multiplication on triples. -/
def mul (a b : BilinearExtension A M N q) : BilinearExtension A M N q :=
  ofTriple q (
    (toTriple q a).1 * (toTriple q b).1,
    (toTriple q a).1 • (toTriple q b).2.1 + (toTriple q b).1 • (toTriple q a).2.1,
    (toTriple q a).1 • (toTriple q b).2.2 + (toTriple q b).1 • (toTriple q a).2.2 +
      q (toTriple q a).2.1 (toTriple q b).2.1 + q (toTriple q b).2.1 (toTriple q a).2.1)

/-- The q-dependent multiplication on the extension. -/
instance instMul : Mul (BilinearExtension A M N q) where
  mul := mul q

/-- The unit for the explicit triple multiplication. -/
instance instOne : One (BilinearExtension A M N q) where
  one := ofTriple q (1, 0, 0)

/-- The commutative-ring laws for the displayed triple multiplication. -/
instance instCommRing : CommRing (BilinearExtension A M N q) :=
  CommRing.ofMinimalAxioms (by sorry) (by sorry) (by sorry) (by sorry) (by sorry) (by sorry)
    (by sorry)

/-- The A-algebra structure induced by the first-coordinate inclusion. -/
instance instAlgebra : Algebra A (BilinearExtension A M N q) where
  toSMul := instSMul q
  algebraMap := {
    toFun := fun a => ofTriple q (a, 0, 0)
    map_one' := by sorry
    map_mul' := by sorry
    map_zero' := by sorry
    map_add' := by sorry
  }
  commutes' := by sorry
  smul_def' := by sorry

/-- The A-algebra inclusion as a ring homomorphism. -/
def inclusion : A →+* BilinearExtension A M N q where
  toFun a := ofTriple q (a, 0, 0)
  map_one' := by sorry
  map_mul' := by sorry
  map_zero' := by sorry
  map_add' := by sorry

/-- The coordinate formula for the q-dependent multiplication. -/
theorem mul_apply (a b : BilinearExtension A M N q) :
    mul q a b =
      ofTriple q (
        (toTriple q a).1 * (toTriple q b).1,
          (toTriple q a).1 • (toTriple q b).2.1 + (toTriple q b).1 • (toTriple q a).2.1,
          (toTriple q a).1 • (toTriple q b).2.2 + (toTriple q b).1 • (toTriple q a).2.2 +
            q (toTriple q a).2.1 (toTriple q b).2.1 +
              q (toTriple q b).2.1 (toTriple q a).2.1) := sorry

/-- The first-coordinate formula for the divided-power extension inclusion. -/
theorem inclusion_apply (a : A) : inclusion q a = ofTriple q (a, 0, 0) := sorry

/-- The first-coordinate projection of the explicit triple ring. -/
def projection : BilinearExtension A M N q →+* A where
  toFun a := (toTriple q a).1
  map_one' := by sorry
  map_mul' := by sorry
  map_zero' := by sorry
  map_add' := by sorry

/-- The projection returns the first coordinate of the underlying triple. -/
theorem projection_apply (a : BilinearExtension A M N q) :
    projection q a = (toTriple q a).1 := sorry

/-- The distinguished ideal obtained by pulling `I` back along the first-coordinate projection. -/
def ideal (I : Ideal A) : Ideal (BilinearExtension A M N q) :=
  I.comap (projection q)

/-- Membership in the distinguished ideal is first-coordinate membership in `I`. -/
theorem ideal_mem_iff (I : Ideal A) (a : BilinearExtension A M N q) :
    a ∈ ideal q I ↔ (toTriple q a).1 ∈ I := sorry

/-- The predecessor divided power, with the negative index convention interpreted as zero. -/
def dpowPred {I : Ideal A} (gamma : DividedPowers I) (n : ℕ) (x : A) : A :=
  if n = 0 then 0 else gamma.dpow (n - 1) x

/-- The predecessor divided power vanishes at index zero. -/
theorem dpowPred_zero {I : Ideal A} (gamma : DividedPowers I) (x : A) :
    dpowPred gamma 0 x = 0 := sorry

/-- At a successor index, the predecessor divided power is the preceding divided power. -/
theorem dpowPred_succ {I : Ideal A} (gamma : DividedPowers I) (n : ℕ) (x : A) :
    dpowPred gamma (n + 1) x = gamma.dpow n x := sorry

/-- The twice-predecessor divided power, with negative indices interpreted as zero. -/
def dpowPredTwo {I : Ideal A} (gamma : DividedPowers I) (n : ℕ) (x : A) : A :=
  if n < 2 then 0 else gamma.dpow (n - 2) x

/-- The twice-predecessor divided power vanishes at index zero. -/
theorem dpowPredTwo_zero {I : Ideal A} (gamma : DividedPowers I) (x : A) :
    dpowPredTwo gamma 0 x = 0 := sorry

/-- The twice-predecessor divided power vanishes at index one. -/
theorem dpowPredTwo_one {I : Ideal A} (gamma : DividedPowers I) (x : A) :
    dpowPredTwo gamma 1 x = 0 := sorry

/-- Two indices above `n`, the twice-predecessor operation is `gamma.dpow n`. -/
theorem dpowPredTwo_add_two {I : Ideal A} (gamma : DividedPowers I) (n : ℕ) (x : A) :
    dpowPredTwo gamma (n + 2) x = gamma.dpow n x := sorry

/-- The explicit divided-power operations on the distinguished ideal. -/
noncomputable def dividedPowers {I : Ideal A} (gamma : DividedPowers I) :
    DividedPowers (ideal q I) := by
  classical
  refine {
    dpow := fun n a =>
      if h : a ∈ ideal q I then
        ofTriple q (
          (gamma.dpow n (toTriple q a).1,
            dpowPred gamma n (toTriple q a).1 • (toTriple q a).2.1,
            dpowPred gamma n (toTriple q a).1 • (toTriple q a).2.2 +
              dpowPredTwo gamma n (toTriple q a).1 •
                q (toTriple q a).2.1 (toTriple q a).2.1))
      else 0
    dpow_null := by sorry
    dpow_zero := by sorry
    dpow_one := by sorry
    dpow_mem := by sorry
    dpow_add := by sorry
    dpow_mul := by sorry
    mul_dpow := by sorry
    dpow_comp := by sorry
  }

/-- The coordinate formula for the explicit divided powers on `J`. -/
theorem dividedPowers_apply {I : Ideal A} (gamma : DividedPowers I)
    (n : ℕ) (x : A) (hx : x ∈ I) (z : M) (w : N) :
    dividedPowers q gamma n (ofTriple q (x, z, w)) =
      ofTriple q (gamma.dpow n x,
        dpowPred gamma n x • z,
        dpowPred gamma n x • w + dpowPredTwo gamma n x • q z z) := sorry

/-- The bundled divided-power morphism carried by the first-coordinate inclusion. -/
def inclusionDPMorphism {I : Ideal A} (gamma : DividedPowers I) :
    DPMorphism gamma (dividedPowers q gamma) where
  toRingHom := inclusion q
  ideal_comp := by sorry
  dpow_comp := by sorry

/-- The underlying ring homomorphism of the bundled inclusion morphism. -/
theorem inclusionDPMorphism_toRingHom {I : Ideal A} (gamma : DividedPowers I) :
    (inclusionDPMorphism q gamma).toRingHom = inclusion q := sorry

/-- The first-coordinate inclusion is a divided-power morphism. -/
theorem inclusion_isDPMorphism
    {A : Type u} {M : Type v} {N : Type w} [CommRing A] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] {I : Ideal A} (gamma : DividedPowers I)
    (q : M →ₗ[A] M →ₗ[A] N) :
    IsDPMorphism gamma (dividedPowers q gamma) (inclusion q) := sorry

end BilinearExtension
end DividedPowers
