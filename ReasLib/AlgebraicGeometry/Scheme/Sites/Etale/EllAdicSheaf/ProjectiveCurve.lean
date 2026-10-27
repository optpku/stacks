/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Genus
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf.Trace
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf.CohomologicalLFunction

/-!
# Point counts on a smooth projective curve over a finite field

Rationality of `L(X, ℚ_[ℓ])`, the integer characteristic polynomial of
`π_X^*` on `H_c^1`, the resulting point-count formula, and the bound
`‖α‖ < q` on complex roots.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Etale AlgebraicGeometry.SchemeOverField
open AlgebraicGeometry.Curve
open scoped AlgebraicGeometry MonoidalCategory Polynomial

namespace AlgebraicGeometry.Scheme.Etale
namespace ZEllSheaf

variable {k : Type u} [Field k] [Fintype k]
variable {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
variable {ℓ : ℕ} [Fact ℓ.Prime]
variable {X : SchemeOverField k} [IsNoetherian X.left]
variable [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]
variable (P : Compactification.Of (Spec (CommRingCat.of k)) X)
variable [Etale (Compactification.Of.ι P)]
variable [∀ G : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
    (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension G]
variable [HasWeakSheafify (Scheme.smallEtaleTopology (Over.left P.obj.right)) AddCommGrpCat.{u}]
variable [HasSheafify (Scheme.smallEtaleTopology (Over.left P.obj.right)) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Scheme.smallEtaleTopology (Over.left P.obj.right)) AddCommGrpCat.{u})]
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]

/-- Compactly supported geometric cohomology in degree one of the constant
`ℚ_[ℓ]`-sheaf on a smooth projective geometrically irreducible curve has
dimension `2 * genus X`. -/
theorem finrank_cohomology_constant_one (hℓp : ℓ ≠ p) :
    Module.finrank ℚ_[ℓ]
        (geometricCohomologyCompactSupportQEll P (constant X.left ℓ) 1) =
      2 * genus X :=
  sorry

/-- The L-function `L(X, ℚ_[ℓ])` of the constant sheaf on a
smooth projective geometrically irreducible curve over a finite field is a
rational function, regular at `0`. -/
theorem lFunction_constant_isRational (hℓp : ℓ ≠ p) :
    ∃ A B : Polynomial ℚ_[ℓ],
      B ≠ 0 ∧ B.eval 0 ≠ 0 ∧
        (B : PowerSeries ℚ_[ℓ]) *
            (constant X.left ℓ).lFunction (constant X.left ℓ).constructible =
          (A : PowerSeries ℚ_[ℓ]) :=
  sorry

/-- Explicit Euler expression of `L(X, ℚ_[ℓ])` in the projective curve case:
`det(1 - π_X^* T | H_c^1) / ((1 - T)(1 - q T))`. -/
theorem lFunction_constant_eq_euler (hℓp : ℓ ≠ p) :
    (constant X.left ℓ).lFunction (constant X.left ℓ).constructible =
      cohomologyEulerFactor P (constant X.left ℓ) 1 *
        PowerSeries.invOfUnit
          (((1 : PowerSeries ℚ_[ℓ]) - PowerSeries.X) *
            ((1 : PowerSeries ℚ_[ℓ]) -
              (Fintype.card k : ℚ_[ℓ]) • PowerSeries.X)) 1 :=
  sorry

/-- The `2g` eigenvalues of `π_X^*` on
`H_c^1(X_k̄, ℚ_[ℓ])` are algebraic integers independent of `ℓ`, encoded as one
monic integer characteristic polynomial of degree `2 * genus X`. -/
theorem geometricFrobeniusH1_charpoly_int (hℓp : ℓ ≠ p) :
    ∃ Q : Polynomial ℤ, Q.Monic ∧ Q.natDegree = 2 * genus X ∧
      LinearMap.charpoly
          (geometricFrobenius_cohomologyCompactSupportQEll P (constant X.left ℓ) 1) =
        Q.map (algebraMap ℤ ℚ_[ℓ]) ∧
      ∀ {ℓ' : ℕ} [Fact ℓ'.Prime], ℓ' ≠ p →
        LinearMap.charpoly
            (geometricFrobenius_cohomologyCompactSupportQEll P (constant X.left ℓ') 1) =
          Q.map (algebraMap ℤ ℚ_[ℓ']) :=
  sorry

/-- If `Q` lifts the characteristic polynomial of `π_X^*` on
`H_c^1` and `[K : k] = n`, then
`#X(K) = 1 - ∑ α^n + q^n` as a complex identity on the roots of `Q`. -/
theorem card_rationalPoints_eq_powerSum (hℓp : ℓ ≠ p) {Q : Polynomial ℤ}
    (hQ_monic : Q.Monic) (hQ_deg : Q.natDegree = 2 * genus X)
    (hQ_charpoly :
      LinearMap.charpoly
          (geometricFrobenius_cohomologyCompactSupportQEll P (constant X.left ℓ) 1) =
        Q.map (algebraMap ℤ ℚ_[ℓ]))
    {n : ℕ} (hn : 0 < n) {K : Type u} [Field K] [Fintype K] [Algebra k K]
    (hK : Module.finrank k K = n) :
    (Nat.card (𝟙_ (SchemeOverField K) ⟶ FieldExtension.Over.baseChange k K X) : ℂ) =
      1 - ((Q.aroots ℂ).map (fun α ↦ α ^ n)).sum + (Fintype.card k : ℂ) ^ n :=
  sorry

/-- Point-count identity in `ℚ_[ℓ]` as the Lefschetz trace of `π_X^{*n}` on
`H_c^1` of the constant sheaf. -/
theorem card_rationalPoints_eq_trace (hℓp : ℓ ≠ p) {n : ℕ} (hn : 0 < n)
    {K : Type u} [Field K] [Fintype K] [Algebra k K]
    (hK : Module.finrank k K = n) :
    (Nat.card (𝟙_ (SchemeOverField K) ⟶ FieldExtension.Over.baseChange k K X) : ℚ_[ℓ]) =
      1 -
          LinearMap.trace ℚ_[ℓ] _
            (geometricFrobenius_cohomologyCompactSupportQEll P (constant X.left ℓ) 1 ^ n) +
        (Fintype.card k : ℚ_[ℓ]) ^ n :=
  sorry

/-- Every complex root `α` of the integer characteristic
polynomial of `π_X^*` on `H_c^1` satisfies `‖α‖ < q`. -/
theorem geometricFrobeniusH1_root_norm_lt (hℓp : ℓ ≠ p) {Q : Polynomial ℤ}
    (hQ_monic : Q.Monic) (hQ_deg : Q.natDegree = 2 * genus X)
    (hQ_charpoly :
      LinearMap.charpoly
          (geometricFrobenius_cohomologyCompactSupportQEll P (constant X.left ℓ) 1) =
        Q.map (algebraMap ℤ ℚ_[ℓ]))
    {α : ℂ} (hα : α ∈ Q.aroots ℂ) :
    ‖α‖ < (Fintype.card k : ℝ) :=
  sorry

end ZEllSheaf
end AlgebraicGeometry.Scheme.Etale
