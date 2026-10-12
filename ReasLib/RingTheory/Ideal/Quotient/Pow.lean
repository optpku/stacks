/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.RingHom.SquareZero

/-!
# Algebra structures on successive ideal-power quotients

This leaf owns the canonical algebra and scalar-tower structures associated
to the quotient transition `R ⧸ I ^ (n + 1) → R ⧸ I ^ n`.
-/

@[expose] public section

universe u

namespace Ideal.Quotient

variable {R : Type u} [CommRing R]

/-- The canonical algebra structure on the quotient by `I ^ n` over the
quotient by `I ^ (n + 1)`, induced by `factorPowSucc`. -/
@[stacks 02HQ "successive ideal-power quotient algebra"]
instance powSuccAlgebra (I : Ideal R) (n : ℕ) :
    Algebra (R ⧸ I ^ (n + 1)) (R ⧸ I ^ n) :=
  RingHom.toAlgebra (factorPowSucc I n)

/-- The quotient maps `R → R ⧸ I ^ (n + 1) → R ⧸ I ^ n` form the canonical
scalar tower. -/
@[stacks 02HQ "successive ideal-power quotient scalar tower"]
instance powSuccIsScalarTower (I : Ideal R) (n : ℕ) :
    IsScalarTower R (R ⧸ I ^ (n + 1)) (R ⧸ I ^ n) :=
  IsScalarTower.of_algebraMap_eq
    (R := R) (S := R ⧸ I ^ (n + 1)) (A := R ⧸ I ^ n) fun _ ↦ rfl

/-- The algebra map of `powSuccAlgebra` is the quotient transition
`factorPowSucc`. -/
@[stacks 02HQ "successive ideal-power quotient algebra"]
theorem powSuccAlgebra_algebraMap (I : Ideal R) (n : ℕ) :
    algebraMap (R ⧸ I ^ (n + 1)) (R ⧸ I ^ n) = factorPowSucc I n :=
  rfl

/-- The transition `R ⧸ I ^ (n + 2) → R ⧸ I ^ (n + 1)` is a square-zero extension. -/
@[stacks 09PS "successive positive ideal-power quotient"]
instance factorPowSuccSuccIsSquareZeroExtension (I : Ideal R) (n : ℕ) :
    (factorPowSucc I (n + 1)).IsSquareZeroExtension := sorry

namespace Power

/-- The transition ideal in `R ⧸ I ^ (n + 1)` is square-zero for positive `n`. -/
@[stacks 09PS "square-zero transition ideal"]
theorem transitionIdeal_sq (I : Ideal R) {n : ℕ} (hn : 0 < n) :
    (Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) (I ^ n)) ^ 2 = ⊥ := sorry

/-- The kernel of the successive power transition is the image of the preceding power. -/
@[stacks 09PS "successive power transition kernel"]
theorem kernel_eq_map (I : Ideal R) (n : ℕ) :
    RingHom.ker (Ideal.Quotient.factorPow I (Nat.le_succ n)) =
      Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) (I ^ n) := sorry

/-- A positive successive power transition has nilpotent kernel. -/
@[stacks 09PS "nilpotent successive power kernel"]
theorem kernel_isNilpotent (I : Ideal R) {n : ℕ} (hn : 0 < n) :
    IsNilpotent (RingHom.ker (Ideal.Quotient.factorPow I (Nat.le_succ n))) := sorry

/-- The kernel of reduction from level `m + 1` to level `1` is the image of `I`. -/
@[stacks 09PS "power reduction kernel"]
theorem toOne_kernel_eq_map (I : Ideal R) (m : ℕ) :
    RingHom.ker
      (Ideal.Quotient.factorPow I (Nat.succ_le_of_lt (Nat.succ_pos m))) =
        Ideal.map (Ideal.Quotient.mk (I ^ (m + 1))) I := sorry

end Power

end Ideal.Quotient
