/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import ReasLib.RingTheory.Sequence.Koszul.Family

@[expose] public section

noncomputable section

universe u

open CategoryTheory HomologicalComplex MvPolynomial
open scoped ZeroObject

namespace MvPolynomial

/-- The residue module `k[x, y] ⧸ (x, y)`. -/
abbrev quotientSpanXY (k : Type u) [Field k] : Type u :=
  MvPolynomial (Fin 2) k ⧸ Ideal.span {(X 0 : MvPolynomial (Fin 2) k), X 1}

/-- The map `R ⟶ R ⊕ 2` with matrix `(y; -x)`, sending `r` to `(r y, -r x)`. -/
def koszulInYNegX (k : Type u) [Field k] :
    ModuleCat.of (MvPolynomial (Fin 2) k) (MvPolynomial (Fin 2) k) ⟶
      ModuleCat.of (MvPolynomial (Fin 2) k) (Fin 2 → MvPolynomial (Fin 2) k) :=
  ModuleCat.ofHom
    (LinearMap.toSpanSingleton (MvPolynomial (Fin 2) k) (Fin 2 → MvPolynomial (Fin 2) k)
      ![X 1, -X 0])

/-- The column `(y; -x)` multiplies a polynomial by `y` in the first coordinate and by `-x` in
the second. -/
theorem koszulInYNegX_apply (k : Type u) [Field k] (r : MvPolynomial (Fin 2) k) :
    (koszulInYNegX k).hom r = ![r * X 1, -(r * X 0)] :=
  sorry

/-- The map `R ⊕ 2 ⟶ R` with matrix `(x, y)`. -/
def koszulOutXY (k : Type u) [Field k] :
    ModuleCat.of (MvPolynomial (Fin 2) k) (Fin 2 → MvPolynomial (Fin 2) k) ⟶
      ModuleCat.of (MvPolynomial (Fin 2) k) (MvPolynomial (Fin 2) k) :=
  ModuleCat.ofHom (koszulLinearForm (X : Fin 2 → MvPolynomial (Fin 2) k))

/-- The row `(x, y)` sends a pair `(a, b)` to `a x + b y`. -/
theorem koszulOutXY_apply (k : Type u) [Field k]
    (v : Fin 2 → MvPolynomial (Fin 2) k) :
    (koszulOutXY k).hom v = v 0 * X 0 + v 1 * X 1 :=
  sorry

/-- The `R`-linear quotient map `R ⟶ R ⧸ (x, y)` realizing evaluation at the origin. -/
def evalAtOriginQuotient (k : Type u) [Field k] :
    ModuleCat.of (MvPolynomial (Fin 2) k) (MvPolynomial (Fin 2) k) ⟶
      ModuleCat.of (MvPolynomial (Fin 2) k) (quotientSpanXY k) :=
  ModuleCat.ofHom (Submodule.mkQ (Ideal.span {(X 0 : MvPolynomial (Fin 2) k), X 1}))

/-- The origin quotient map sends a polynomial to its class in `R ⧸ (x, y)`. -/
theorem evalAtOriginQuotient_apply (k : Type u) [Field k]
    (f : MvPolynomial (Fin 2) k) :
    (evalAtOriginQuotient k).hom f = Submodule.Quotient.mk f :=
  sorry

/-- Degree-`n` term of the displayed augmented Koszul sequence on `k[x, y]`. -/
def augmentedKoszulXYTerm (k : Type u) [Field k] :
    ℕ → ModuleCat (MvPolynomial (Fin 2) k)
  | 0 => ModuleCat.of (MvPolynomial (Fin 2) k) (quotientSpanXY k)
  | 1 => ModuleCat.of (MvPolynomial (Fin 2) k) (MvPolynomial (Fin 2) k)
  | 2 => ModuleCat.of (MvPolynomial (Fin 2) k) (Fin 2 → MvPolynomial (Fin 2) k)
  | 3 => ModuleCat.of (MvPolynomial (Fin 2) k) (MvPolynomial (Fin 2) k)
  | _ => 0

/-- Differentials of the displayed augmented Koszul sequence on `k[x, y]`. -/
def augmentedKoszulXYDiff (k : Type u) [Field k] :
    ∀ n, augmentedKoszulXYTerm k (n + 1) ⟶ augmentedKoszulXYTerm k n
  | 0 => evalAtOriginQuotient k
  | 1 => koszulOutXY k
  | 2 => koszulInYNegX k
  | _ => 0

/-- Consecutive differentials of the displayed augmented Koszul sequence compose to zero. -/
theorem augmentedKoszulXYDiff_sq (k : Type u) [Field k] (n : ℕ) :
    augmentedKoszulXYDiff k (n + 1) ≫ augmentedKoszulXYDiff k n = 0 :=
  sorry

/-- The displayed augmented Koszul sequence
`0 ⟶ R ⟶ R ⊕ 2 ⟶ R ⟶ k ⟶ 0` as a chain complex, with `k` in degree `0`. -/
def augmentedKoszulXY (k : Type u) [Field k] :
    ChainComplex (ModuleCat (MvPolynomial (Fin 2) k)) ℕ :=
  ChainComplex.of (augmentedKoszulXYTerm k) (augmentedKoszulXYDiff k)
    (augmentedKoszulXYDiff_sq k)

/-- Terms of `augmentedKoszulXY` are the displayed modules `k`, `R`, `R ⊕ 2`, `R`, then `0`. -/
theorem augmentedKoszulXY_X (k : Type u) [Field k] :
    (augmentedKoszulXY k).X = augmentedKoszulXYTerm k :=
  sorry

/-- The differential `d (n + 1) n` of `augmentedKoszulXY` is `augmentedKoszulXYDiff n`. -/
theorem augmentedKoszulXY_d (k : Type u) [Field k] (n : ℕ) :
    (augmentedKoszulXY k).d (n + 1) n = augmentedKoszulXYDiff k n :=
  sorry

/-- The augmented Koszul sequence on `k[x, y]` is acyclic. -/
theorem augmentedKoszulXY_acyclic (k : Type u) [Field k] :
    (augmentedKoszulXY k).Acyclic :=
  sorry

end MvPolynomial
