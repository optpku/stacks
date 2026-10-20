module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.Tor.Notation

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped ModuleTor

namespace MvPolynomial

/-- For the coefficient ring with polynomial action through `constantCoeff`, the inclusion
`idealOfVars σ A ^ (n + 1) ≤ idealOfVars σ A ^ n` induces the zero map on `Tor` in every
homological degree. -/
@[stacks 08RE]
theorem tor_map_pow_idealOfVars_eq_zero
    {A : Type u} [CommRing A] {σ : Type u} (i n : ℕ) :
    ((CategoryTheory.Tor (ModuleCat (MvPolynomial σ A)) i).obj
      ((ModuleCat.restrictScalars (MvPolynomial.constantCoeff : MvPolynomial σ A →+* A)).obj
        (ModuleCat.of A A))).map
      (ModuleCat.ofHom (Submodule.inclusion
        (Ideal.pow_le_pow_right (I := MvPolynomial.idealOfVars σ A) n.le_succ))) = 0 := sorry

/-- Over a field `k`, the Tor objects of `R ⧸ Ideal.span {X 0, X 2}` and
`R ⧸ Ideal.span {X 1, X 2}` over `R = MvPolynomial (Fin 3) k` are nonzero
exactly in degrees `0` and `1`. -/
@[stacks 0FWR]
theorem tor_quotient_span_XZ_YZ_not_isZero_iff {k : Type u} [Field k] (n : ℕ) :
    ¬ IsZero
        (Tor⁽n⁾[MvPolynomial (Fin 3) k](MvPolynomial (Fin 3) k ⧸
            Ideal.span {(X 0 : MvPolynomial (Fin 3) k), X 2},
          MvPolynomial (Fin 3) k ⧸
            Ideal.span {(X 1 : MvPolynomial (Fin 3) k), X 2})) ↔
      n = 0 ∨ n = 1 :=
  sorry

/-- The degree-`0` Tor object of `R ⧸ Ideal.span {X 0, X 2}` and
`R ⧸ Ideal.span {X 1, X 2}` over `R = MvPolynomial (Fin 3) k` is nonzero. -/
theorem tor_quotient_span_XZ_YZ_not_isZero_zero {k : Type u} [Field k] :
    ¬ IsZero
        (Tor⁽0⁾[MvPolynomial (Fin 3) k](MvPolynomial (Fin 3) k ⧸
            Ideal.span {(X 0 : MvPolynomial (Fin 3) k), X 2},
          MvPolynomial (Fin 3) k ⧸
            Ideal.span {(X 1 : MvPolynomial (Fin 3) k), X 2})) :=
  sorry

/-- The degree-`1` Tor object of `R ⧸ Ideal.span {X 0, X 2}` and
`R ⧸ Ideal.span {X 1, X 2}` over `R = MvPolynomial (Fin 3) k` is nonzero. -/
theorem tor_quotient_span_XZ_YZ_not_isZero_one {k : Type u} [Field k] :
    ¬ IsZero
        (Tor⁽1⁾[MvPolynomial (Fin 3) k](MvPolynomial (Fin 3) k ⧸
            Ideal.span {(X 0 : MvPolynomial (Fin 3) k), X 2},
          MvPolynomial (Fin 3) k ⧸
            Ideal.span {(X 1 : MvPolynomial (Fin 3) k), X 2})) :=
  sorry

/-- For every `n ≥ 2`, the degree-`n` Tor object of `R ⧸ Ideal.span {X 0, X 2}` and
`R ⧸ Ideal.span {X 1, X 2}` over `R = MvPolynomial (Fin 3) k` vanishes. -/
theorem tor_quotient_span_XZ_YZ_isZero_of_two_le {k : Type u} [Field k] {n : ℕ}
    (hn : 2 ≤ n) :
    IsZero
      (Tor⁽n⁾[MvPolynomial (Fin 3) k](MvPolynomial (Fin 3) k ⧸
          Ideal.span {(X 0 : MvPolynomial (Fin 3) k), X 2},
        MvPolynomial (Fin 3) k ⧸
          Ideal.span {(X 1 : MvPolynomial (Fin 3) k), X 2})) :=
  sorry

/-- Over a field `k`, the Tor objects of `R ⧸ Ideal.span {X 0, X 2}` and
`R ⧸ Ideal.span {X 1, X 2}` over `R = MvPolynomial (Fin 3) k`, extended by zero
to negative integer degrees, are nonzero exactly in degrees `0` and `1`. -/
theorem tor_quotient_span_XZ_YZ_not_isZero_int_iff {k : Type u} [Field k] (i : ℤ) :
    (∃ n : ℕ, i = n ∧
        ¬ IsZero
            (Tor⁽n⁾[MvPolynomial (Fin 3) k](MvPolynomial (Fin 3) k ⧸
                Ideal.span {(X 0 : MvPolynomial (Fin 3) k), X 2},
              MvPolynomial (Fin 3) k ⧸
                Ideal.span {(X 1 : MvPolynomial (Fin 3) k), X 2}))) ↔
      i = 0 ∨ i = 1 :=
  sorry


end MvPolynomial
