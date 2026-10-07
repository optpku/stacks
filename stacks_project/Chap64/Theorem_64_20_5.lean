module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.KrullDimension
public import stacks_project.Chap64.Theorem_64_20_5_Trace

/-!
# Lefschetz trace formula for Q_ℓ-sheaves

Finite-dimensionality, cohomological support, and the geometric Frobenius
trace identity for compactly supported cohomology of a `ℚ_[ℓ]`-sheaf on a
separated finite-type scheme over a finite field.
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

/-- Theorem 64.20.5 (1). For a separated finite-type scheme `X` over a finite
field `k` and a `ℚ_[ℓ]`-sheaf `F` on `X`, each compactly supported geometric
cohomology group `H_c^i(X_k̄, F)` is finite-dimensional over `ℚ_[ℓ]`. -/
@[stacks 03V2]
theorem finiteDimensional_geometricCohomologyCompactSupportQEll (i : ℕ) :
    FiniteDimensional ℚ_[ℓ] (geometricCohomologyCompactSupportQEll P F i) :=
  sorry

/-- Theorem 64.20.5 (2). The same groups are nonzero only for
`0 ≤ i ≤ 2 * dim X`. Indexing by `ℕ` already encodes `0 ≤ i`; a nonzero
`finrank` forces `(i : WithBot ℕ∞) ≤ 2 • topologicalKrullDim X.left`. -/
@[stacks 03V2]
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

/-- Theorem 64.20.5 (3). The Lefschetz identity
`∑_{x ∈ X(k)} Tr(π_x | F_x̄) = ∑_i (-1)^i Tr(π_X^* | H_c^i(X_k̄, F))`
holds in `ℚ_[ℓ]`, as equality of `traceGeometricFrobeniusStalksQEll` with
`traceGeometricFrobenius_cohomologyCompactSupportQEll`. -/
@[stacks 03V2]
theorem lefschetzTraceFormula_qellSheaf :
    traceGeometricFrobeniusStalksQEll F =
      traceGeometricFrobenius_cohomologyCompactSupportQEll P F :=
  sorry

end ZEllSheaf
end AlgebraicGeometry.Scheme.Etale
