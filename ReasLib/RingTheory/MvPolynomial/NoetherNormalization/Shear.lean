module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.MvPolynomial.NoetherNormalization.Triangular

@[expose] public section

/-!
# Invertible triangular coordinate changes

This leaf adds the subtraction inverse and algebra equivalence available over a
commutative ring to the semiring-level additive triangular map.
-/

open MvPolynomial

namespace MvPolynomial.NoetherNormalization

universe u

variable {R : Type u} [CommRing R]
variable {n : ℕ}

/-- The triangular coordinate map that subtracts the prescribed powers used by `addShear`. -/
@[stacks 051N "subtractive triangular polynomial coordinate map"]
noncomputable def subShear (e : Fin n → ℕ) :
    MvPolynomial (Fin (n + 1)) R →ₐ[R] MvPolynomial (Fin (n + 1)) R :=
  MvPolynomial.aeval
    (Fin.snoc (fun i : Fin n ↦ X i.castSucc - X (Fin.last n) ^ e i) (X (Fin.last n)))

/-- `subShear` sends a non-last coordinate to that coordinate minus the prescribed last-variable
power. -/
@[simp]
theorem subShear_X_castSucc (e : Fin n → ℕ) (i : Fin n) :
    subShear e (X i.castSucc) =
      MvPolynomial.X (R := R) i.castSucc -
        MvPolynomial.X (R := R) (Fin.last n) ^ e i := sorry

/-- `subShear` fixes the last coordinate. -/
@[simp]
theorem subShear_X_last (e : Fin n → ℕ) :
    subShear e (X (Fin.last n)) = MvPolynomial.X (R := R) (Fin.last n) := sorry

/-- `addShear` and `subShear` compose to the identity in the forward order. -/
theorem addShear_comp_subShear (e : Fin n → ℕ) :
    (addShear e).comp (subShear e) =
      AlgHom.id R (MvPolynomial (Fin (n + 1)) R) := sorry

/-- `addShear` and `subShear` compose to the identity in the reverse order. -/
theorem subShear_comp_addShear (e : Fin n → ℕ) :
    (subShear e).comp (addShear e) =
      AlgHom.id R (MvPolynomial (Fin (n + 1)) R) := sorry

/-- The triangular polynomial automorphism induced by `addShear`, with inverse `subShear`. -/
@[stacks 051N "invertible triangular polynomial coordinate change"]
noncomputable def shear (e : Fin n → ℕ) :
    MvPolynomial (Fin (n + 1)) R ≃ₐ[R] MvPolynomial (Fin (n + 1)) R :=
  AlgEquiv.ofAlgHom (addShear e) (subShear e)
    (addShear_comp_subShear e) (subShear_comp_addShear e)

/-- `shear` evaluates a non-last coordinate by the additive triangular formula. -/
@[simp]
theorem shear_X_castSucc (e : Fin n → ℕ) (i : Fin n) :
    shear e (X i.castSucc) =
      MvPolynomial.X (R := R) i.castSucc +
        MvPolynomial.X (R := R) (Fin.last n) ^ e i := sorry

/-- `shear` fixes the last coordinate. -/
@[simp]
theorem shear_X_last (e : Fin n → ℕ) :
    shear e (X (Fin.last n)) = MvPolynomial.X (R := R) (Fin.last n) := sorry

/-- The inverse of `shear` evaluates a non-last coordinate by the subtractive triangular formula. -/
@[simp]
theorem shear_symm_X_castSucc (e : Fin n → ℕ) (i : Fin n) :
    (shear e).symm (X i.castSucc) =
      MvPolynomial.X (R := R) i.castSucc -
        MvPolynomial.X (R := R) (Fin.last n) ^ e i := sorry

/-- The inverse of `shear` fixes the last coordinate. -/
@[simp]
theorem shear_symm_X_last (e : Fin n → ℕ) :
    (shear e).symm (X (Fin.last n)) = MvPolynomial.X (R := R) (Fin.last n) := sorry

end MvPolynomial.NoetherNormalization
