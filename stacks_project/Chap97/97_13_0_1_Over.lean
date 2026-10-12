/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import ReasLib.RingTheory.Algebra.UniversalFiniteFree

/-!
# Free finite-dimensional algebras over a ring

An explicit commutative unital `R`-algebra structure on the distinguished free module
`Fin d → R`, with unit the first basis vector. This is the functor-of-points value of
`Spec (CoefficientRing d)`.
-/

@[expose] public section

open TensorProduct

noncomputable section

universe u

namespace UniversalFiniteFreeAlgebra

/-- The distinguished unit vector `e₁ = (1, 0, …, 0)` in `Fin d → R`. -/
abbrev unitVec (R : Type u) [CommRing R] (d : ℕ+) : Fin d → R :=
  Pi.single 0 1

/-- A free `d`-dimensional algebra over `R`: a commutative unital `R`-algebra structure
on the distinguished free module `Fin d → R` whose unit is `unitVec`. -/
structure Over (R : Type u) [CommRing R] (d : ℕ+) where
  /-- Bilinear multiplication `m : (Fin d → R) →ₗ[R] (Fin d → R) →ₗ[R] (Fin d → R)`. -/
  mul : (Fin d → R) →ₗ[R] (Fin d → R) →ₗ[R] (Fin d → R)
  /-- Multiplication is associative. -/
  mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)
  /-- Multiplication is commutative. -/
  mul_comm : ∀ x y, mul x y = mul y x
  /-- The first basis vector is a left unit. -/
  one_mul : ∀ x, mul (unitVec R d) x = x

namespace Over

variable {R : Type u} [CommRing R] {d : ℕ+}

/-- Structure constants of `m`, so `m (Pi.single i 1) (Pi.single j 1) k`. -/
def coeff (m : Over R d) (i j k : Fin d) : R :=
  m.mul (Pi.single i 1) (Pi.single j 1) k

/-- The tensor form `m : (Fin d → R) ⊗[R] (Fin d → R) →ₗ[R] (Fin d → R)` of bilinear
multiplication. -/
def mul' (m : Over R d) : (Fin d → R) ⊗[R] (Fin d → R) →ₗ[R] (Fin d → R) :=
  TensorProduct.lift m.mul

/-- Pointwise multiplication obtained by evaluating universal structure constants along `ψ`. -/
def mulFn (ψ : CoefficientRing d →+* R) (x y : Fin d → R) : Fin d → R :=
  fun k ↦ ∑ i : Fin d, ∑ j : Fin d, x i * y j * ψ (coefficient d i j k)

/-- The free `d`-dimensional algebra over `R` obtained by base change of the universal
multiplication along `ψ : CoefficientRing d →+* R`. -/
def ofRingHom (ψ : CoefficientRing d →+* R) : Over R d where
  mul := LinearMap.mk₂ R (mulFn ψ) sorry sorry sorry sorry
  mul_assoc := sorry
  mul_comm := sorry
  one_mul := sorry

/-- Evaluation of a polynomial in the structure constants of `m`. -/
def aevalCoeff (m : Over R d) : PolynomialRing d →ₐ[ℤ] R :=
  MvPolynomial.aeval fun (i, j, k) ↦ m.coeff i j k

/-- The structure-constant evaluation of `m` vanishes on the universal relation ideal. -/
theorem aevalCoeff_mem_relationIdeal (m : Over R d) (p : PolynomialRing d)
    (hp : p ∈ relationIdeal d) : m.aevalCoeff p = 0 :=
  sorry

/-- The unique classifying map `CoefficientRing d →+* R` sending universal structure
constants to those of `m`. -/
def toRingHom (m : Over R d) : CoefficientRing d →+* R :=
  Ideal.Quotient.lift (relationIdeal d) m.aevalCoeff.toRingHom
    fun p hp ↦ aevalCoeff_mem_relationIdeal m p hp

/-- The universal free `d`-dimensional algebra `m_univ` over `CoefficientRing d`. -/
def universal (d : ℕ+) : Over (CoefficientRing d) d where
  mul := multiplication d
  mul_assoc := sorry
  mul_comm := sorry
  one_mul := sorry

/-- Ring maps out of the universal coefficient ring correspond to free `d`-dimensional
algebras over `R`. -/
def ringHomEquiv (R : Type u) [CommRing R] (d : ℕ+) :
    (CoefficientRing d →+* R) ≃ Over R d where
  toFun := ofRingHom
  invFun := toRingHom
  left_inv := sorry
  right_inv := sorry

/-- Base change of structure constants along `f : R →+* S`. -/
def map {S : Type u} [CommRing S] (f : R →+* S) (m : Over R d) : Over S d :=
  ofRingHom (f.comp m.toRingHom)

/-- The structure map of `m`, sending a scalar to that scalar times the unit vector. -/
def algebraMapFn (m : Over R d) : R → Fin d → R :=
  fun r ↦ m.mul (r • unitVec R d) (unitVec R d)

/-- The structure map of `m` preserves multiplication with respect to `m.mul`. -/
theorem algebraMapFn_mul (m : Over R d) (r s : R) :
    m.mul (m.algebraMapFn r) (m.algebraMapFn s) = m.algebraMapFn (r * s) :=
  sorry

/-- The structure map of `m` is the `R`-scalar action on the unit vector. -/
theorem algebraMapFn_apply (m : Over R d) (r : R) :
    m.algebraMapFn r = r • unitVec R d :=
  sorry

/-- The defining laws of a free `d`-dimensional algebra: associativity, commutativity,
and the unit vector. -/
theorem spec (m : Over R d) :
    (∀ x y z, m.mul (m.mul x y) z = m.mul x (m.mul y z)) ∧
      (∀ x y, m.mul x y = m.mul y x) ∧
        ∀ x, m.mul (unitVec R d) x = x :=
  sorry

/-- Associativity of structure constants of `m`. -/
theorem coeff_assoc (m : Over R d) (i j k n : Fin d) :
    (∑ l : Fin d, m.coeff i j l * m.coeff l k n) =
      ∑ l : Fin d, m.coeff i l n * m.coeff j k l :=
  sorry

/-- Symmetry of structure constants of `m` in the two input indices. -/
theorem coeff_comm (m : Over R d) (i j k : Fin d) :
    m.coeff i j k = m.coeff j i k :=
  sorry

/-- Coefficients against the unit vector are the Kronecker delta. -/
theorem coeff_unit (m : Over R d) (i j : Fin d) :
    m.coeff i 0 j = if i = j then 1 else 0 :=
  sorry

/-- Products of basis vectors expand in the structure constants of `m`. -/
theorem mul_basis (m : Over R d) (i j : Fin d) :
    m.mul (Pi.single i 1) (Pi.single j 1) =
      ∑ k : Fin d, m.coeff i j k • Pi.single k (1 : R) :=
  sorry

/-- The first basis vector is also a right unit for `m`. -/
theorem mul_one (m : Over R d) (x : Fin d → R) : m.mul x (unitVec R d) = x :=
  sorry

/-- Structure constants of `ofRingHom ψ` are the images of the universal coefficients. -/
theorem ofRingHom_coeff (ψ : CoefficientRing d →+* R) (i j k : Fin d) :
    (ofRingHom ψ).coeff i j k = ψ (coefficient d i j k) :=
  sorry

/-- `ringHomEquiv` sends a classifying map to the corresponding algebra structure. -/
theorem ringHomEquiv_apply (ψ : CoefficientRing d →+* R) :
    ringHomEquiv R d ψ = ofRingHom ψ :=
  sorry

/-- The inverse of `ringHomEquiv` recovers the classifying map of an algebra structure. -/
theorem ringHomEquiv_symm_apply (m : Over R d) :
    (ringHomEquiv R d).symm m = m.toRingHom :=
  sorry

end Over

end UniversalFiniteFreeAlgebra
