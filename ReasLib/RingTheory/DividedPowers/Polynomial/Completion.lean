/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DividedPowers.Polynomial
public import ReasLib.RingTheory.AdicCompletion.Nat

@[expose] public section

universe u

namespace DPPolynomial.Completion

variable (p : ℕ) (R : Type u) [CommRing R] (κ : Type u)

/-- Extend each coefficient of a finitely supported variable family to the completion. -/
noncomputable def coefficientLinear : (κ →₀ R) →ₗ[R] κ →₀ AdicCompletion.Nat.ring p R :=
  Finsupp.mapRange.linearMap (Algebra.linearMap R (AdicCompletion.Nat.ring p R))

/-- Extend coefficients of a divided-power polynomial to the completed coefficient ring. -/
noncomputable def coefficientMap :
    DPPolynomial R κ →+* DPPolynomial (AdicCompletion.Nat.ring p R) κ :=
  (DividedPowerAlgebra.map (AdicCompletion.Nat.ring p R) (coefficientLinear p R κ)).toRingHom

/-- Coefficient extension sends a constant to its canonical completed coefficient. -/
theorem coefficientMap_algebraMap (r : R) :
    coefficientMap p R κ (algebraMap R (DPPolynomial R κ) r) =
      algebraMap (AdicCompletion.Nat.ring p R)
        (DPPolynomial (AdicCompletion.Nat.ring p R) κ) (AdicCompletion.of _ R r) := sorry

/-- Coefficient extension preserves each indexed divided-power variable. -/
theorem coefficientMap_X (i : κ) :
    coefficientMap p R κ (DPPolynomial.X R i) =
      DPPolynomial.X (AdicCompletion.Nat.ring p R) i := sorry

/-- Complete the concrete coefficient-extension map. -/
noncomputable def comparison :
    AdicCompletion.Nat.ring p (DPPolynomial R κ) →+*
      AdicCompletion.Nat.ring p (DPPolynomial (AdicCompletion.Nat.ring p R) κ) :=
  AdicCompletion.Nat.map p (coefficientMap p R κ)

/-- Completing the coefficients before completing the divided-power polynomial algebra
does not change the completed ring, for an arbitrary variable family. -/
theorem comparison_bijective : Function.Bijective (comparison p R κ) := sorry

end DPPolynomial.Completion
