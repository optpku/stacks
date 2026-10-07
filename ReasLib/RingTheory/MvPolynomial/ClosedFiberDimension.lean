module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal

universe u v

noncomputable section

@[expose] public section

open MvPolynomial

namespace MvPolynomial

/-- For an injective finite-type domain extension of a polynomial ring over an algebraically closed
field, the nonzero fiber over the origin has dimension between the total dimension minus the
number of variables and the total dimension minus one. -/
theorem ringKrullDim_map_idealOfVars_bounds
    {k : Type u} {A : Type v} [Field k] [IsAlgClosed k] [CommRing A] [IsDomain A]
    {n : ℕ} [NeZero n] [Algebra (MvPolynomial (Fin n) k) A]
    [Algebra.FiniteType (MvPolynomial (Fin n) k) A]
    (hinj : Function.Injective (algebraMap (MvPolynomial (Fin n) k) A))
    (hne : Ideal.map (algebraMap (MvPolynomial (Fin n) k) A) (idealOfVars (Fin n) k) ≠ ⊤) :
    ringKrullDim
        (A ⧸ Ideal.map (algebraMap (MvPolynomial (Fin n) k) A) (idealOfVars (Fin n) k)) + 1 ≤
      ringKrullDim A ∧
    ringKrullDim A ≤
      ringKrullDim
          (A ⧸ Ideal.map (algebraMap (MvPolynomial (Fin n) k) A) (idealOfVars (Fin n) k)) + n :=
  sorry

/-- The finite-type chart sending each generator `X i` to itself when `(i : ℕ) + r < n` and to
`X 0 * X i` otherwise. -/
def fiberDimHom (k : Type u) [CommRing k] (n : ℕ) [NeZero n] (r : ℕ) :
    MvPolynomial (Fin n) k →+* MvPolynomial (Fin n) k :=
  (aeval fun i : Fin n ↦ if (i : ℕ) + r < n then X i else X (0 : Fin n) * X i).toRingHom

/-- The generators evaluated by `fiberDimHom`. -/
theorem fiberDimHom_X (k : Type u) [CommRing k] (n : ℕ) [NeZero n] (r : ℕ) (i : Fin n) :
    fiberDimHom k n r (X i) = if (i : ℕ) + r < n then X i else X 0 * X i :=
  sorry

/-- `fiberDimHom k n r` is injective over a field. -/
theorem fiberDimHom_injective (k : Type u) [Field k] (n : ℕ) [NeZero n] (r : ℕ) :
    Function.Injective (fiberDimHom k n r) :=
  sorry

/-- `fiberDimHom k n r` is of finite type. -/
theorem fiberDimHom_finiteType (k : Type u) [CommRing k] (n : ℕ) [NeZero n] (r : ℕ) :
    (fiberDimHom k n r).FiniteType :=
  sorry

/-- Over a nontrivial coefficient ring, the origin ideal remains proper after extension along
`fiberDimHom k n r`. -/
theorem map_idealOfVars_fiberDimHom_ne_top
    (k : Type u) [CommRing k] [Nontrivial k] (n : ℕ) [NeZero n] (r : ℕ) :
    Ideal.map (fiberDimHom k n r) (idealOfVars (Fin n) k) ≠ ⊤ :=
  sorry

/-- For `r < n`, the closed fiber of `fiberDimHom` has Krull dimension `r`. -/
theorem ringKrullDim_map_fiberDimHom {k : Type u} [Field k] [IsAlgClosed k]
    {n r : ℕ} [NeZero n] (hr : r < n) :
    ringKrullDim
        (MvPolynomial (Fin n) k ⧸ Ideal.map (fiberDimHom k n r) (idealOfVars (Fin n) k)) = r :=
  sorry

/-- The chart sending `X 0` to `X 0 * X 1` and `X 1` to `X 0 * X 2`. -/
def unequalComponentsHom (k : Type u) [CommRing k] :
    MvPolynomial (Fin 2) k →+* MvPolynomial (Fin 3) k :=
  (aeval fun i ↦ if i = 0 then X 0 * X 1 else X 0 * X 2).toRingHom

/-- `unequalComponentsHom` sends `X 0` to `X 0 * X 1`. -/
theorem unequalComponentsHom_X_zero (k : Type u) [CommRing k] :
    unequalComponentsHom k (X (0 : Fin 2)) = X (0 : Fin 3) * X 1 :=
  sorry

/-- `unequalComponentsHom` sends `X 1` to `X 0 * X 2`. -/
theorem unequalComponentsHom_X_one (k : Type u) [CommRing k] :
    unequalComponentsHom k (X (1 : Fin 2)) = X (0 : Fin 3) * X 2 :=
  sorry

/-- `unequalComponentsHom` is injective over a field. -/
theorem unequalComponentsHom_injective (k : Type u) [Field k] :
    Function.Injective (unequalComponentsHom k) :=
  sorry

/-- `unequalComponentsHom` is of finite type. -/
theorem unequalComponentsHom_finiteType (k : Type u) [CommRing k] :
    (unequalComponentsHom k).FiniteType :=
  sorry

/-- Over a nontrivial coefficient ring, the origin ideal remains proper after extension along
`unequalComponentsHom`. -/
theorem map_idealOfVars_unequalComponentsHom_ne_top
    (k : Type u) [CommRing k] [Nontrivial k] :
    Ideal.map (unequalComponentsHom k) (idealOfVars (Fin 2) k) ≠ ⊤ :=
  sorry

/-- The ideal `(X 0)` in `MvPolynomial (Fin 3) k`. -/
def planePrime (k : Type u) [CommRing k] : Ideal (MvPolynomial (Fin 3) k) :=
  Ideal.span {X (0 : Fin 3)}

/-- The ideal `(X 1, X 2)` in `MvPolynomial (Fin 3) k`. -/
def linePrime (k : Type u) [CommRing k] : Ideal (MvPolynomial (Fin 3) k) :=
  Ideal.span {X (1 : Fin 3), X 2}

/-- The extended origin ideal is contained in `planePrime`. -/
theorem map_idealOfVars_le_planePrime (k : Type u) [CommRing k] :
    Ideal.map (unequalComponentsHom k) (idealOfVars (Fin 2) k) ≤ planePrime k :=
  sorry

/-- The extended origin ideal is contained in `linePrime`. -/
theorem map_idealOfVars_le_linePrime (k : Type u) [CommRing k] :
    Ideal.map (unequalComponentsHom k) (idealOfVars (Fin 2) k) ≤ linePrime k :=
  sorry

/-- `planePrime` is prime over a field. -/
instance planePrime.instIsPrime (k : Type u) [Field k] : (planePrime k).IsPrime :=
  sorry

/-- `linePrime` is prime over a field. -/
instance linePrime.instIsPrime (k : Type u) [Field k] : (linePrime k).IsPrime :=
  sorry

/-- `planePrime` is a minimal prime of the closed-fiber ideal. -/
theorem planePrime_mem_minimalPrimes (k : Type u) [Field k] :
    planePrime k ∈
      (Ideal.map (unequalComponentsHom k) (idealOfVars (Fin 2) k)).minimalPrimes :=
  sorry

/-- `linePrime` is a minimal prime of the closed-fiber ideal. -/
theorem linePrime_mem_minimalPrimes (k : Type u) [Field k] :
    linePrime k ∈
      (Ideal.map (unequalComponentsHom k) (idealOfVars (Fin 2) k)).minimalPrimes :=
  sorry

/-- The quotient by `planePrime` has Krull dimension `2`. -/
theorem ringKrullDim_quotient_planePrime (k : Type u) [Field k] :
    ringKrullDim (MvPolynomial (Fin 3) k ⧸ planePrime k) = 2 :=
  sorry

/-- The quotient by `linePrime` has Krull dimension `1`. -/
theorem ringKrullDim_quotient_linePrime (k : Type u) [Field k] :
    ringKrullDim (MvPolynomial (Fin 3) k ⧸ linePrime k) = 1 :=
  sorry

/-- The closed fiber of `unequalComponentsHom` has minimal components of unequal Krull dimension. -/
theorem ringKrullDim_planePrime_ne_linePrime {k : Type u} [Field k] [IsAlgClosed k] :
    planePrime k ∈
        (Ideal.map (unequalComponentsHom k) (idealOfVars (Fin 2) k)).minimalPrimes ∧
    linePrime k ∈
        (Ideal.map (unequalComponentsHom k) (idealOfVars (Fin 2) k)).minimalPrimes ∧
    ringKrullDim (MvPolynomial (Fin 3) k ⧸ planePrime k) ≠
      ringKrullDim (MvPolynomial (Fin 3) k ⧸ linePrime k) :=
  sorry

end MvPolynomial
