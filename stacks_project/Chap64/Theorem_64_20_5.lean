/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf.Trace
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf.CohomologicalLFunction

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

/- Theorem 64.20.5 (1). Finite-dimensionality of geometric compactly
supported rational ℓ-adic cohomology. -/
@[stacks 03V2] #check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.instFiniteDimensional_geometricCohomologyCompactSupportQEll
  P F : ∀ i : ℕ, FiniteDimensional ℚ_[ℓ] (geometricCohomologyCompactSupportQEll P F i))

/- Theorem 64.20.5 (2). The cohomological degree bound. -/
@[stacks 03V2] #check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.support_geometricCohomologyCompactSupportQEll
  P F : ∀ i : ℕ,
    Module.finrank ℚ_[ℓ] (geometricCohomologyCompactSupportQEll P F i) ≠ 0 →
      (i : WithBot ℕ∞) ≤ 2 • topologicalKrullDim X.left)

/- Vanishing above twice the Krull dimension. -/
#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.vanishing_geometricCohomologyCompactSupportQEll
  P F : ∀ i : ℕ,
    2 • topologicalKrullDim X.left < (i : WithBot ℕ∞) →
      Module.finrank ℚ_[ℓ] (geometricCohomologyCompactSupportQEll P F i) = 0)

/- Computation of the alternating trace from a cohomological vanishing bound. -/
#check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.traceGeometricFrobenius_cohomologyCompactSupportQEll_eq_sum
  P F : ∀ N : ℕ,
    (∀ i, N < i →
      Module.finrank ℚ_[ℓ] (geometricCohomologyCompactSupportQEll P F i) = 0) →
    traceGeometricFrobenius_cohomologyCompactSupportQEll P F =
      ∑ i ∈ Finset.range (N + 1), (-1 : ℚ_[ℓ]) ^ i *
        LinearMap.trace ℚ_[ℓ] _
          (geometricFrobenius_cohomologyCompactSupportQEll P F i))

/- Theorem 64.20.5. The rational ℓ-adic Lefschetz trace identity, with ℓ
invertible in the finite base field. -/
@[stacks 03V2] #check (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.lefschetzTraceFormula_qellSheaf
  P F : (ℓ : k) ≠ 0 →
    traceGeometricFrobeniusStalksQEll F =
      traceGeometricFrobenius_cohomologyCompactSupportQEll P F)

end ZEllSheaf
end AlgebraicGeometry.Scheme.Etale
