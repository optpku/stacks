/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Algebra.Group.Invertible.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Polynomial.Laurent

@[expose] public section

noncomputable section

open scoped LaurentPolynomial

namespace LaurentPolynomial

/-- The monomial unit `C u * T n` in `(ℤ[T;T⁻¹])ˣ`. -/
def monomialUnit (u : ℤˣ) (n : ℤ) : (ℤ[T;T⁻¹])ˣ :=
  Units.map C.toMonoidHom u * unitOfInvertible (T n)

/-- The underlying Laurent polynomial of `monomialUnit u n` is `C u * T n`. -/
theorem monomialUnit_coe (u : ℤˣ) (n : ℤ) :
    (monomialUnit u n).val = C (u : ℤ) * T n :=
  sorry

/-- Monomial units `± T n` are uniquely determined by the coefficient unit and exponent. -/
theorem monomialUnit_eq_iff (u v : ℤˣ) (m n : ℤ) :
    monomialUnit u n = monomialUnit v m ↔ u = v ∧ n = m :=
  sorry

/-- The group homomorphism sending `(u, n)` to the monomial unit `C u * T n.toAdd`. -/
def unitsMulHom : ℤˣ × Multiplicative ℤ →* (ℤ[T;T⁻¹])ˣ where
  toFun p := monomialUnit p.fst p.snd.toAdd
  map_one' := sorry
  map_mul' := sorry

/-- `unitsMulHom` evaluates as `monomialUnit` on a pair. -/
theorem unitsMulHom_apply (u : ℤˣ) (n : Multiplicative ℤ) :
    unitsMulHom (u, n) = monomialUnit u n.toAdd :=
  sorry

/-- A Laurent polynomial over `ℤ` is a unit exactly when it is a monomial with an integer-unit coefficient. -/
theorem isUnit_iff {f : ℤ[T;T⁻¹]} :
    IsUnit f ↔ ∃ (u : ℤˣ) (n : ℤ), f = C (u : ℤ) * T n :=
  sorry

/-- The multiplicative unit group of `ℤ[T;T⁻¹]` is equivalent to `ℤˣ × Multiplicative ℤ`. -/
def intUnitsEquiv : (ℤ[T;T⁻¹])ˣ ≃* ℤˣ × Multiplicative ℤ where
  toFun f :=
    let n := WithBot.unbotD 0 f.val.degree
    (if f.val.coeff n = -1 then -1 else 1, Multiplicative.ofAdd n)
  invFun := unitsMulHom
  left_inv := sorry
  right_inv := sorry
  map_mul' := sorry

/-- The classification equivalence sends the monomial unit `C u * T n` to `(u, n)`. -/
theorem intUnitsEquiv_apply (u : ℤˣ) (n : ℤ) :
    intUnitsEquiv (monomialUnit u n) = (u, Multiplicative.ofAdd n) :=
  sorry

/-- The inverse classification reconstructs the monomial unit `C u * T n.toAdd`. -/
theorem intUnitsEquiv_symm_apply (u : ℤˣ) (n : Multiplicative ℤ) :
    intUnitsEquiv.symm (u, n) = monomialUnit u n.toAdd :=
  sorry

/-- The additive group of units of `ℤ[T;T⁻¹]` is equivalent to `Additive ℤˣ × ℤ`. -/
def intUnitsAddEquiv : Additive (ℤ[T;T⁻¹])ˣ ≃+ Additive ℤˣ × ℤ :=
  (MulEquiv.toAdditive intUnitsEquiv).trans <|
    (AddEquiv.prodAdditive ℤˣ (Multiplicative ℤ)).trans
      (AddEquiv.prodCongr (AddEquiv.refl (Additive ℤˣ)) (AddEquiv.additiveMultiplicative ℤ))

/-- `intUnitsAddEquiv` is `intUnitsEquiv` after forgetting multiplication. -/
theorem intUnitsAddEquiv_apply (f : (ℤ[T;T⁻¹])ˣ) :
    intUnitsAddEquiv (Additive.ofMul f) =
      (Additive.ofMul (intUnitsEquiv f).fst, (intUnitsEquiv f).snd.toAdd) :=
  sorry

end LaurentPolynomial
