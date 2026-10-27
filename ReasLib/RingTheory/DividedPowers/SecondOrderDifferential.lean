/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.DividedPowers.BilinearExtension
public import ReasLib.RingTheory.DividedPowers.TrivSqZeroExt
public import Mathlib.Algebra.Category.Ring.Basic

/-!
# Two-direction bilinear extensions

A bilinear pairing gives an extension with two independent module coordinates and a
second-order coordinate. The two coordinate inclusions from a square-zero extension
preserve its full coordinate divided-power ideal.
-/

@[expose] public section

noncomputable section

universe u v w

namespace DividedPowers.SecondOrderDifferential

variable {A : Type u} {M : Type v} {N : Type w}
variable [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
variable (w : M →ₗ[A] M →ₗ[A] N)

/-- The cross pairing on two copies of a module pairs the first and second directions. -/
def crossPairing : (M × M) →ₗ[A] (M × M) →ₗ[A] N := by
  refine {
    toFun x := (w x.1).comp (LinearMap.snd A M M)
    map_add' := ?_
    map_smul' := ?_ }
  all_goals sorry

/-- The two-direction extension associated to a bilinear pairing. -/
abbrev Carrier := BilinearExtension A (M × M) N (crossPairing w)

/-- The extension element with the four specified coordinates. -/
def ofCoordinates (a : A) (ω₁ ω₂ : M) (η : N) : Carrier w :=
  BilinearExtension.ofTriple (crossPairing w) (a, (ω₁, ω₂), η)

/-- The four coordinates of an extension element. -/
def coordinates (z : Carrier w) : A × M × M × N :=
  let z := BilinearExtension.toTriple (crossPairing w) z
  (z.1, z.2.1.1, z.2.1.2, z.2.2)

/-- Reading the coordinates of a specified element recovers its entries. -/
@[simp] theorem coordinates_ofCoordinates (a : A) (ω₁ ω₂ : M) (η : N) :
    coordinates w (ofCoordinates w a ω₁ ω₂ η) = (a, ω₁, ω₂, η) := rfl

/-- Every extension element is recovered from its coordinates. -/
theorem ofCoordinates_coordinates (z : Carrier w) :
    ofCoordinates w (coordinates w z).1 (coordinates w z).2.1
      (coordinates w z).2.2.1 (coordinates w z).2.2.2 = z := rfl

/-- Multiplication has the two cross terms prescribed by the pairing. -/
theorem mul_apply (a b : A) (ω₁ ω₂ τ₁ τ₂ : M) (η θ : N) :
    ofCoordinates w a ω₁ ω₂ η * ofCoordinates w b τ₁ τ₂ θ =
      ofCoordinates w (a * b) (a • τ₁ + b • ω₁) (a • τ₂ + b • ω₂)
        (a • θ + b • η + w ω₁ τ₂ + w τ₁ ω₂) := rfl

/-- The commutative ring of the two-direction extension. -/
def ring : CommRingCat := CommRingCat.of (Carrier w)

/-- The projection to the function coordinate. -/
def projection : Carrier w →+* A := BilinearExtension.projection (crossPairing w)

/-- The full coordinate ideal is the inverse image of the original ideal. -/
def ideal (I : Ideal A) : Ideal (Carrier w) := BilinearExtension.ideal (crossPairing w) I

/-- Membership in the full coordinate ideal depends only on the function coordinate. -/
theorem mem_ideal_iff (I : Ideal A) (z : Carrier w) :
    z ∈ ideal w I ↔ (coordinates w z).1 ∈ I := Iff.rfl

/-- The divided powers on the full coordinate ideal. -/
def dividedPowers {I : Ideal A} (γ : DividedPowers I) : DividedPowers (ideal w I) :=
  BilinearExtension.dividedPowers (crossPairing w) γ

/-- The four coordinate formula for divided powers, with negative indices interpreted as zero. -/
theorem dividedPowers_apply {I : Ideal A} (γ : DividedPowers I) (n : ℕ)
    (a : A) (ha : a ∈ I) (ω₁ ω₂ : M) (η : N) :
    dividedPowers w γ n (ofCoordinates w a ω₁ ω₂ η) =
      ofCoordinates w (γ.dpow n a) (BilinearExtension.dpowPred γ n a • ω₁)
        (BilinearExtension.dpowPred γ n a • ω₂)
        (BilinearExtension.dpowPred γ n a • η +
          BilinearExtension.dpowPredTwo γ n a • w ω₁ ω₂) :=
  BilinearExtension.dividedPowers_apply (crossPairing w) γ n a ha (ω₁, ω₂) η

variable [Module Aᵐᵒᵖ M] [IsCentralScalar A M]

/-- The first-direction inclusion of the square-zero extension. -/
def q01 : TrivSqZeroExt A M →+* Carrier w := by
  refine {
    toFun z := ofCoordinates w z.fst z.snd 0 0
    map_one' := ?_
    map_mul' := ?_
    map_zero' := ?_
    map_add' := ?_ }
  all_goals sorry

/-- The diagonal inclusion of a square-zero extension for an alternating pairing. -/
def q02 (hw : ∀ ω, w ω ω = 0) : TrivSqZeroExt A M →+* Carrier w := by
  refine {
    toFun z := ofCoordinates w z.fst z.snd z.snd 0
    map_one' := ?_
    map_mul' := ?_
    map_zero' := ?_
    map_add' := ?_ }
  all_goals sorry

/-- The first-direction inclusion has zero second and second-order coordinates. -/
theorem q01_apply (z : TrivSqZeroExt A M) :
    q01 w z = ofCoordinates w z.fst z.snd 0 0 := rfl

/-- The diagonal inclusion repeats the module coordinate and has zero second-order coordinate. -/
theorem q02_apply (hw : ∀ ω, w ω ω = 0) (z : TrivSqZeroExt A M) :
    q02 w hw z = ofCoordinates w z.fst z.snd z.snd 0 := rfl

/-- The first-direction inclusion preserves coordinate divided powers on the full ideals. -/
theorem q01_isDPMorphism {I : Ideal A} (γ : DividedPowers I) :
    IsDPMorphism (TrivSqZeroExt.dividedPowers M γ) (dividedPowers w γ) (q01 w) := sorry

/-- The diagonal inclusion for an alternating pairing preserves coordinate divided powers. -/
theorem q02_isDPMorphism (hw : ∀ ω, w ω ω = 0) {I : Ideal A} (γ : DividedPowers I) :
    IsDPMorphism (TrivSqZeroExt.dividedPowers M γ) (dividedPowers w γ) (q02 w hw) := sorry

end DividedPowers.SecondOrderDifferential
