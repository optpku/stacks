/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Reduction
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChosenFppf.QuasiSeparated
public import Mathlib.Data.List.TFAE

/-!
# Absolute separation criteria for the reduction of a formal algebraic space
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry.IsFormalAlgebraicSpace

/-- The reduction of a formal algebraic space is absolutely separated exactly
when all affine tests have affine fibre products with surjective canonical
`ℤ`-tensor maps on global sections, expressed as a list of equivalent conditions. -/
theorem tfae_separated {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [Fact (ChosenBigSite.IsSizeClosed 𝒮)]
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    List.TFAE [ChosenBigFppfSite.IsSeparated (reduction X),
      forallAffinePullbackAffineSurjective X] := sorry

/-- The reduction of a formal algebraic space is a separated algebraic space
if and only if fibre products of morphisms from affine schemes to `X` are
affine with surjective `sectionTensor`. -/
theorem isSeparated_reduction_iff
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [Fact (ChosenBigSite.IsSizeClosed 𝒮)]
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    ChosenBigFppfSite.IsSeparated (reduction X) ↔
      forallAffinePullbackAffineSurjective X := sorry

/-- The reduction of a formal algebraic space is quasi-separated if and only if
fibre products of arbitrary morphisms from quasi-compact schemes are
quasi-compact, equivalently if the same holds for affine schemes. -/
theorem tfae_quasiSeparated {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [Fact (ChosenBigSite.IsSizeClosed 𝒮)]
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    List.TFAE [ChosenBigFppfSite.IsQuasiSeparated (reduction X),
      forallQuasiCompactPullback X, forallAffineQuasiCompactPullback X] := sorry

/-- The reduction of a formal algebraic space is a quasi-separated algebraic
space if and only if fibre products of morphisms from quasi-compact schemes
to `X` are quasi-compact. -/
theorem isQuasiSeparated_reduction_iff_forallQuasiCompactPullback
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [Fact (ChosenBigSite.IsSizeClosed 𝒮)]
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    ChosenBigFppfSite.IsQuasiSeparated (reduction X) ↔
      forallQuasiCompactPullback X := sorry

/-- Fibre products of morphisms from quasi-compact schemes to a formal
algebraic space are quasi-compact if and only if the same holds for morphisms
from affine schemes. -/
theorem forallQuasiCompactPullback_iff_forallAffineQuasiCompactPullback
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [Fact (ChosenBigSite.IsSizeClosed 𝒮)]
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    forallQuasiCompactPullback X ↔ forallAffineQuasiCompactPullback X := sorry

/-- The reduction of a formal algebraic space is a quasi-separated algebraic
space if and only if fibre products of morphisms from affine schemes to `X`
are quasi-compact. -/
theorem isQuasiSeparated_reduction_iff_forallAffineQuasiCompactPullback
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [Fact (ChosenBigSite.IsSizeClosed 𝒮)]
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    ChosenBigFppfSite.IsQuasiSeparated (reduction X) ↔
      forallAffineQuasiCompactPullback X := sorry

end AlgebraicGeometry.IsFormalAlgebraicSpace
