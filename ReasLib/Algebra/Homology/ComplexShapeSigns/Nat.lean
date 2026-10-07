module

public import Mathlib.Algebra.Homology.ComplexShapeSigns
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 07MB

# Tensor signs for nonnegative cochain degrees

The Cech cochain construction uses the upward shape on `ℕ`.  This leaf gives that shape the same
Koszul sign character already available for integer cochains, so tensor and Alexander--Whitney
components can be stated without a proof-local sign instance.
-/

@[expose] public section

open ComplexShape

namespace ComplexShape.upNat

/-- The alternating sign character on nonnegative cochain degrees. -/
@[stacks 07MB "nonnegative cochain tensor sign character"]
def signCharacter : Multiplicative ℕ →* ℤˣ :=
  MonoidHom.mk' (fun n : ℕ ↦ (-1 : ℤˣ) ^ n) (pow_add (-1 : ℤˣ))

/-- The standard Koszul tensor signs for the upward natural-number shape. -/
@[stacks 07MB "nonnegative cochain tensor signs"]
instance tensorSigns : (ComplexShape.up ℕ).TensorSigns where
  ε' := signCharacter
  rel_add p q r hpq := by
    change p + 1 = q at hpq
    change p + r + 1 = q + r
    lia
  add_rel p q r hpq := by
    change p + 1 = q at hpq
    change r + p + 1 = r + q
    lia
  ε'_succ := by
    rintro p _ rfl
    change (-1 : ℤˣ) ^ Nat.succ p = -((-1 : ℤˣ) ^ p)
    calc
      (-1 : ℤˣ) ^ Nat.succ p = ((-1 : ℤˣ) ^ p) * (-1 : ℤˣ) := by
        exact pow_succ _ _
      _ = -(((-1 : ℤˣ) ^ p) * 1) := by
        rw [mul_neg]
      _ = -((-1 : ℤˣ) ^ p) := by
        simp

/-- The displayed formula for the nonnegative cochain sign character. -/
@[simp]
theorem epsilon_apply (n : ℕ) :
    (ComplexShape.up ℕ).ε n = (-1 : ℤˣ) ^ n := rfl

end ComplexShape.upNat

end
