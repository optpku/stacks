/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Sober
public import ReasLib.AlgebraicGeometry.ChowGroup.Total
public import ReasLib.AlgebraicGeometry.ChowGroup.Relative.Cycle

@[expose] public section

open CategoryTheory
open scoped BigOperators DirectSum TensorProduct Topology

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

/-- Relative dimensions of generic points of a quasi-compact locally finite-type scheme. -/
noncomputable def relativeDimensionDegrees {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (X : Over S) [LocallyOfFiniteType X.hom]
    [CompactSpace X.left] : Finset ℤ :=
  let hNoeth : IsNoetherian X.left :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian X.hom }
  (genericPoints.finite
      (@finite_irreducibleComponents_of_isNoetherian X.left hNoeth)).toFinset.image
    (X.hom.relativeDimensionFunction δ)

/-- `relativeDimensionDegrees` is the image of the finite set of generic points under the
relative dimension function. -/
theorem relativeDimensionDegrees_def {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (X : Over S) [LocallyOfFiniteType X.hom]
    [CompactSpace X.left] :
    relativeDimensionDegrees δ X =
      (genericPoints.finite
          (@finite_irreducibleComponents_of_isNoetherian X.left
            { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian X.hom })).toFinset.image
        (X.hom.relativeDimensionFunction δ) :=
  sorry

/-- The total fundamental class `[Y] ∈ CH_*(Y)` assembled from the degree-`n` pieces
`[Y]_n` on the finitely many relative dimensions of generic points. -/
noncomputable def totalFundamentalClass {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (Y : Over S) [LocallyOfFiniteType Y.hom]
    [CompactSpace Y.left] : Total δ Y :=
  ∑ n ∈ relativeDimensionDegrees δ Y,
    DirectSum.of _ n (RelativeChow.fundamentalClass δ Y n)

/-- The degree-`n` summand of `totalFundamentalClass` is `[Y]_n`. -/
theorem totalFundamentalClass_of {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ] (Y : Over S) [LocallyOfFiniteType Y.hom]
    [CompactSpace Y.left] (n : ℤ) :
    (totalFundamentalClass δ Y n) =
      if n ∈ relativeDimensionDegrees δ Y then RelativeChow.fundamentalClass δ Y n else 0 :=
  sorry

end AlgebraicGeometry.ChowGroup
