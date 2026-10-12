/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.HopkinsLevitzki
public import ReasLib.RingTheory.Ideal.AssociatedGraded.Module
public import ReasLib.RingTheory.Ideal.HilbertSamuel.Finiteness
public import ReasLib.RingTheory.Polynomial.Numerical
import Mathlib.Tactic.CrossRefAttribute

/-!
# Hilbert Function of an Associated Graded Module

The homogeneous pieces of `gr_I(M)` are modules over `R ⧸ I`.  This file
owns their finiteness, length comparison, and the generalized Hilbert
polynomial statement; no local-ring hypothesis is built into the core API.
-/

@[expose] public section

noncomputable section

universe u v

open Filter

namespace Ideal.AssociatedGraded

variable {R : Type u} [CommRing R]

/-- The length of the `n`-th associated graded piece over `R ⧸ I` is the
Hilbert--Samuel `φ`-value. -/
@[stacks 00K8 "associated-graded piece length"]
theorem piece_length_eq_phi (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] (n : ℕ) :
    Module.length (R ⧸ I) (piece I M n) =
      Ideal.hilbertSamuelPhi I M n := sorry

/-- Every associated graded quotient piece of a finite module over a
Noetherian ring is finite over `R ⧸ I`. -/
@[stacks 00K8 "associated-graded piece finiteness"]
theorem piece_finite (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] [IsNoetherianRing R] [Module.Finite R M] (n : ℕ) :
    Module.Finite (R ⧸ I) (piece I M n) := sorry

/-- The length function of the associated graded pieces, extended by zero to
negative integer degrees. -/
@[stacks 00K8 "associated graded Hilbert function"]
noncomputable def intGradeLength (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] : ℤ → ℕ∞ :=
  fun n ↦ if 0 ≤ n then
    Module.length (R ⧸ I) (piece I M n.toNat)
  else 0

/-- The integer-extended associated graded Hilbert function vanishes in every
negative degree. -/
@[stacks 00K8 "associated-graded negative Hilbert value"]
theorem intGradeLength_eq_zero_of_neg (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] {n : ℤ} (hn : n < 0) :
    intGradeLength I M n = 0 := sorry

/-- The associated graded Hilbert function agrees with `φ` in every
nonnegative degree. -/
@[stacks 00K8 "associated-graded Hilbert value"]
theorem intGradeLength_eq_phi_of_nonneg (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] {n : ℤ} (hn : 0 ≤ n) :
    intGradeLength I M n = Ideal.hilbertSamuelPhi I M n.toNat := sorry

/-- The associated graded Hilbert function and the Hilbert--Samuel
`φ`-function agree eventually on `ℤ`. -/
@[stacks 00K8 "associated-graded eventual Hilbert comparison"]
theorem intGradeLength_eventuallyEq_phi (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] :
    (fun n : ℤ ↦ ((intGradeLength I M n).toNat : ℚ)) =ᶠ[atTop]
      fun n : ℤ ↦ ((Ideal.hilbertSamuelPhi I M n.toNat).toNat : ℚ) := sorry

/-- For a finite module over a Noetherian ring with Artinian quotient, the
associated graded Hilbert function is a numerical polynomial. -/
@[stacks 00K8 "associated graded Hilbert polynomial"]
theorem intGradeLength_isNumericalPolynomial (I : Ideal R) (M : Type v)
    [AddCommGroup M] [Module R M] [IsNoetherianRing R] [Module.Finite R M]
    [IsArtinianRing (R ⧸ I)] :
    IsNumericalPolynomial
      (fun n : ℤ ↦ ((intGradeLength I M n).toNat : ℚ)) := sorry

end Ideal.AssociatedGraded
