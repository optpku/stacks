/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import stacks_project.Chap64.Definition_64_19_1_EulerFactor
public import stacks_project.Chap64.Definition_64_19_1_LFunction
public import stacks_project.Chap64.Definition_64_19_3_Stalk

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf.LFunction

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

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.localEulerFactor :
  ∀ (F : ZEllSheaf X.left ℓ) (hF : F.IsConstructible) (x : closedPoints X.left),
    PowerSeries ℚ_[ℓ])

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.localEulerFactor_spec :
  ∀ (F : ZEllSheaf X.left ℓ) (hF : F.IsConstructible) (x : closedPoints X.left),
    F.localEulerFactor hF x =
      LinearMap.eulerFactor (F.geometricFrobeniusStalk x) (X.hom.residueDegree x.1))

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.constantCoeff_localEulerFactor :
  ∀ (F : ZEllSheaf X.left ℓ) (hF : F.IsConstructible)
    (x : closedPoints X.left),
    PowerSeries.constantCoeff (F.localEulerFactor hF x) = 1)

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.lFunction :
  ∀ (F : ZEllSheaf X.left ℓ) (hF : F.IsConstructible),
    PowerSeries ℚ_[ℓ])

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.lFunction_coeff :
  ∀ (F : ZEllSheaf X.left ℓ) (hF : F.IsConstructible) (n : ℕ),
    PowerSeries.coeff n (F.lFunction hF) =
      PowerSeries.coeff n
        (∏ x : {x : closedPoints X.left // X.hom.residueDegree x.1 ≤ n},
          F.localEulerFactor hF x.1))

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.lFunction_spec :
  ∀ (F : ZEllSheaf X.left ℓ) (hF : F.IsConstructible),
    F.lFunction hF =
      PowerSeries.mk fun n ↦
        PowerSeries.coeff n
          (∏ x : {x : closedPoints X.left // X.hom.residueDegree x.1 ≤ n},
            F.localEulerFactor hF x.1))

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.localEulerFactor_coeff_eq_zero_of_lt_residueDegree :
  ∀ (F : ZEllSheaf X.left ℓ) (hF : F.IsConstructible) (x : closedPoints X.left) (n : ℕ)
    (hn : 0 < n) (hx : n < X.hom.residueDegree x.1),
    PowerSeries.coeff n (F.localEulerFactor hF x) = 0)

#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.lFunction_coeff_eq_prod_of_le :
  ∀ (F : ZEllSheaf X.left ℓ) (hF : F.IsConstructible) (n m : ℕ)
    (hnm : n ≤ m),
    PowerSeries.coeff n (F.lFunction hF) =
      PowerSeries.coeff n
        (∏ x : {x : closedPoints X.left // X.hom.residueDegree x.1 ≤ m},
          F.localEulerFactor hF x.1))

end AlgebraicGeometry.Scheme.Etale.ZEllSheaf
