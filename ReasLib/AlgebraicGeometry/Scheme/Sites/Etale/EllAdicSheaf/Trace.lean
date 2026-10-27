/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf.Frobenius
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf.Stalk.Rational
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.GeometricCompactSupport
public import ReasLib.AlgebraicGeometry.Scheme.OverField.FinitePoints

/-!
# Geometric Frobenius traces of Q_ℓ-sheaves

Named `k`-point geometric Frobenius `π_x` and the two `ℚ_[ℓ]`-valued trace
sums appearing in the Lefschetz identity for compactly supported geometric
cohomology.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Etale AlgebraicGeometry.SchemeOverField
open scoped AlgebraicGeometry MonoidalCategory

namespace AlgebraicGeometry.Scheme.Etale
namespace ZEllSheaf

variable {k : Type u} [Field k] [Fintype k]
variable {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
variable {ℓ : ℕ} [Fact ℓ.Prime]
variable {X : SchemeOverField k} [Scheme.Hom.FiniteType X.hom] [IsSeparated X.hom]
  [IsNoetherian X.left]
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]

section StalkTrace

variable (F : ZEllSheaf X.left ℓ)

/-- Geometric Frobenius `π_x` on the `ℚ_[ℓ]`-stalk at a `k`-rational point,
obtained by specialising closed-point geometric Frobenius along
`closedPointOfRationalPoint`. -/
def geometricFrobeniusStalkRational (x : 𝟙_ (SchemeOverField k) ⟶ X) :
    Module.End ℚ_[ℓ]
      (F.qellStalk (geometricPointOverClosedPoint X (closedPointOfRationalPoint x))) :=
  F.geometricFrobeniusStalk (closedPointOfRationalPoint x)

/-- Unfolding of `k`-point geometric Frobenius as closed-point geometric
Frobenius at `closedPointOfRationalPoint x`. -/
theorem geometricFrobeniusStalkRational_spec (x : 𝟙_ (SchemeOverField k) ⟶ X) :
    geometricFrobeniusStalkRational F x =
      F.geometricFrobeniusStalk (closedPointOfRationalPoint x) :=
  rfl

/-- Stalk-side Lefschetz trace `∑_{x ∈ X(k)} Tr(π_x | F_x̄)` in `ℚ_[ℓ]`. -/
def traceGeometricFrobeniusStalksQEll : ℚ_[ℓ] :=
  ∑ᶠ x : (𝟙_ (SchemeOverField k) ⟶ X),
    LinearMap.trace ℚ_[ℓ] _ (geometricFrobeniusStalkRational F x)

/-- Unfolding of the stalk-side `ℚ_[ℓ]` trace as a finitely supported sum over
morphisms `𝟙_ ⟶ X`. -/
theorem traceGeometricFrobeniusStalksQEll_spec :
    traceGeometricFrobeniusStalksQEll F =
      ∑ᶠ x : (𝟙_ (SchemeOverField k) ⟶ X),
        LinearMap.trace ℚ_[ℓ] _ (geometricFrobeniusStalkRational F x) :=
  rfl

end StalkTrace

section CohomologyTrace

variable (P : Compactification.Of (Spec (CommRingCat.of k)) X)
variable [Etale (Compactification.Of.ι P)]
variable [∀ G : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
    (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension G]
variable [HasWeakSheafify (Scheme.smallEtaleTopology (Over.left P.obj.right)) AddCommGrpCat.{u}]
variable [HasSheafify (Scheme.smallEtaleTopology (Over.left P.obj.right)) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Scheme.smallEtaleTopology (Over.left P.obj.right)) AddCommGrpCat.{u})]
variable [∀ Z : Scheme.{u},
    HasInjectiveResolutions (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u})]
variable (F : ZEllSheaf X.left ℓ)

/-- Cohomological Lefschetz trace
`∑_i (-1)^i Tr(π_X^* | H_c^i(X_k̄, F))` in `ℚ_[ℓ]`. -/
def traceGeometricFrobenius_cohomologyCompactSupportQEll : ℚ_[ℓ] :=
  ∑ᶠ i : ℕ, (-1 : ℚ_[ℓ]) ^ i *
    LinearMap.trace ℚ_[ℓ] _ (geometricFrobenius_cohomologyCompactSupportQEll P F i)

/-- Unfolding of the cohomological `ℚ_[ℓ]` trace as a signed finitely supported
sum of traces of `π_X^*` on `H_c^i(X_k̄, F ⊗ ℚ_[ℓ])`. -/
theorem traceGeometricFrobenius_cohomologyCompactSupportQEll_spec :
    traceGeometricFrobenius_cohomologyCompactSupportQEll P F =
      ∑ᶠ i : ℕ, (-1 : ℚ_[ℓ]) ^ i *
        LinearMap.trace ℚ_[ℓ] _
          (geometricFrobenius_cohomologyCompactSupportQEll P F i) :=
  rfl

/-- Nonzero compactly supported geometric rational ℓ-adic cohomology occurs
only in degrees at most twice the Krull dimension of the scheme. -/
theorem support_geometricCohomologyCompactSupportQEll (i : ℕ)
    (h : Module.finrank ℚ_[ℓ] (geometricCohomologyCompactSupportQEll P F i) ≠ 0) :
    (i : WithBot ℕ∞) ≤ 2 • topologicalKrullDim X.left :=
  sorry

/-- Compactly supported geometric `ℚ_[ℓ]`-cohomology vanishes in degrees
strictly larger than twice the Krull dimension. -/
theorem vanishing_geometricCohomologyCompactSupportQEll (i : ℕ)
    (h : 2 • topologicalKrullDim X.left < (i : WithBot ℕ∞)) :
    Module.finrank ℚ_[ℓ] (geometricCohomologyCompactSupportQEll P F i) = 0 :=
  sorry

/-- If compactly supported geometric `ℚ_[ℓ]`-cohomology vanishes above degree
`N`, the cohomological Lefschetz trace is the corresponding finite alternating
sum. -/
theorem traceGeometricFrobenius_cohomologyCompactSupportQEll_eq_sum (N : ℕ)
    (hN : ∀ i, N < i →
      Module.finrank ℚ_[ℓ] (geometricCohomologyCompactSupportQEll P F i) = 0) :
    traceGeometricFrobenius_cohomologyCompactSupportQEll P F =
      ∑ i ∈ Finset.range (N + 1), (-1 : ℚ_[ℓ]) ^ i *
        LinearMap.trace ℚ_[ℓ] _
          (geometricFrobenius_cohomologyCompactSupportQEll P F i) :=
  sorry

/-- When ℓ is invertible in the finite base field, the sum of geometric
Frobenius traces on rational-point stalks equals the alternating trace on
geometric compactly supported rational ℓ-adic cohomology. -/
theorem lefschetzTraceFormula_qellSheaf (hℓ : (ℓ : k) ≠ 0) :
    traceGeometricFrobeniusStalksQEll F =
      traceGeometricFrobenius_cohomologyCompactSupportQEll P F :=
  sorry

end CohomologyTrace

end ZEllSheaf
end AlgebraicGeometry.Scheme.Etale
