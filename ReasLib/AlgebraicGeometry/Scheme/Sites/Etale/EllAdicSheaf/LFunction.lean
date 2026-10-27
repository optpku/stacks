/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf.Frobenius
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf.Stalk.Rational
public import ReasLib.LinearAlgebra.Determinant.EulerFactor
public import ReasLib.AlgebraicGeometry.Scheme.OverField.LFunction

/-!
# L-functions of Q_ℓ-sheaves

The Euler product
`∏_{x ∈ |X|} det(1 - π_x^* T^{deg x} | F_x̄)⁻¹`
in `ℚ_[ℓ]⟦T⟧`, assembled coefficientwise from `LinearMap.eulerFactor` of
geometric Frobenius over closed points of bounded residue degree.
-/

@[expose] public section

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.SchemeOverField
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Etale.ZEllSheaf

variable {k : Type u} [Field k] [Fintype k]
variable {ℓ : ℕ} [Fact (Nat.Prime ℓ)]
variable {X : SchemeOverField k} [Scheme.Hom.FiniteType X.hom] [IsNoetherian X.left]
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]
variable (F : ZEllSheaf X.left ℓ)

/-- The local Euler factor `det(1 - π_x^* T^{deg x} | F_x̄)⁻¹` in `ℚ_[ℓ]⟦T⟧`. -/
def localEulerFactor (hF : F.IsConstructible) (x : closedPoints X.left) :
    PowerSeries ℚ_[ℓ] :=
  LinearMap.eulerFactor (F.geometricFrobeniusStalk x) (X.hom.residueDegree x.1)

/-- The local Euler factor is `LinearMap.eulerFactor` of geometric Frobenius at
residue degree `deg x`. -/
theorem localEulerFactor_spec (hF : F.IsConstructible) (x : closedPoints X.left) :
    F.localEulerFactor hF x =
      LinearMap.eulerFactor (F.geometricFrobeniusStalk x) (X.hom.residueDegree x.1) :=
  rfl

/-- The constant coefficient of each local Euler factor is `1`. -/
theorem constantCoeff_localEulerFactor (hF : F.IsConstructible)
    (x : closedPoints X.left) :
    PowerSeries.constantCoeff (F.localEulerFactor hF x) = 1 := sorry

/-- The L-function of a constructible `ℚ_[ℓ]`-sheaf, as the Euler product over
closed points of the local factors `det(1 - π_x^* T^{deg x} | F_x̄)⁻¹`. -/
def lFunction (hF : F.IsConstructible) : PowerSeries ℚ_[ℓ] :=
  PowerSeries.mk fun n ↦
    PowerSeries.coeff n
      (∏ x : {x : closedPoints X.left // X.hom.residueDegree x.1 ≤ n},
        F.localEulerFactor hF x.1)

/-- The coefficient of `T^n` in `lFunction` is the corresponding coefficient of
the finite product of Euler factors over closed points of residue degree at
most `n`. -/
theorem lFunction_coeff (hF : F.IsConstructible) (n : ℕ) :
    PowerSeries.coeff n (F.lFunction hF) =
      PowerSeries.coeff n
        (∏ x : {x : closedPoints X.left // X.hom.residueDegree x.1 ≤ n},
          F.localEulerFactor hF x.1) := by
  exact PowerSeries.coeff_mk n _

/-- The L-function is the Euler product over closed points of the local
factors `det(1 - π_x^* T^{deg x} | F_x̄)⁻¹`, realised coefficientwise by
finite products over residue degree at most `n`. -/
theorem lFunction_spec (hF : F.IsConstructible) :
    F.lFunction hF =
      PowerSeries.mk fun n ↦
        PowerSeries.coeff n
          (∏ x : {x : closedPoints X.left // X.hom.residueDegree x.1 ≤ n},
            F.localEulerFactor hF x.1) := rfl

/-- A positive coefficient below the residue degree vanishes in a local Euler factor. -/
theorem localEulerFactor_coeff_eq_zero_of_lt_residueDegree
    (hF : F.IsConstructible) (x : closedPoints X.left) (n : ℕ)
    (hn : 0 < n) (hx : n < X.hom.residueDegree x.1) :
    PowerSeries.coeff n (F.localEulerFactor hF x) = 0 := sorry

/-- The coefficient of degree `n` in the L-function is unchanged by any cutoff
on residue degrees at least `n`. -/
theorem lFunction_coeff_eq_prod_of_le (hF : F.IsConstructible) (n m : ℕ)
    (hnm : n ≤ m) :
    PowerSeries.coeff n (F.lFunction hF) =
      PowerSeries.coeff n
        (∏ x : {x : closedPoints X.left // X.hom.residueDegree x.1 ≤ m},
          F.localEulerFactor hF x.1) := sorry

end AlgebraicGeometry.Scheme.Etale.ZEllSheaf
