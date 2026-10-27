/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Reduction
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.EtaleCover
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChosenFppf.QuasiCompact

/-!
# Quasi-compactness characterizations for formal algebraic spaces

Characterizations of quasi-compactness of the reduction of a formal algebraic
space: a finite étale affine atlas, or a single affine étale cover.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite
open AlgebraicGeometry.IsFormalAlgebraicSpace

noncomputable section

universe u v

namespace AlgebraicGeometry.IsFormalAlgebraicSpace

/-- For a formal algebraic space over a size-closed chosen big fppf site,
quasi-compactness of its reduction, existence of a finite affine étale atlas,
and existence of a single affine formal étale cover are equivalent. -/
theorem tfae_quasiCompact {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    [Fact (ChosenBigSite.IsSizeClosed 𝒮)]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    List.TFAE [ChosenBigFppfSite.IsQuasiCompact (reduction X),
      HasFiniteAffineEtaleAtlas X, HasAffineEtaleCover X] := sorry

/-- The reduction of a formal algebraic space is a quasi-compact algebraic
space if and only if `X` admits an étale affine atlas with
finite index. -/
theorem isQuasiCompact_reduction_iff_hasFiniteAffineEtaleAtlas
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    [Fact (ChosenBigSite.IsSizeClosed 𝒮)]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    ChosenBigFppfSite.IsQuasiCompact (reduction X) ↔
      HasFiniteAffineEtaleAtlas X := sorry

/-- A formal algebraic space admits a finite étale affine atlas if and only if
it admits a single representable étale surjection from an affine formal
algebraic space. -/
theorem hasFiniteAffineEtaleAtlas_iff_hasAffineEtaleCover
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    [Fact (ChosenBigSite.IsSizeClosed 𝒮)]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    HasFiniteAffineEtaleAtlas X ↔ HasAffineEtaleCover X := sorry

/-- The reduction of a formal algebraic space is a quasi-compact algebraic
space if and only if there is a representable étale surjection from an affine
formal algebraic space. -/
theorem isQuasiCompact_reduction_iff_hasAffineEtaleCover
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    [Fact (ChosenBigSite.IsSizeClosed 𝒮)]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    ChosenBigFppfSite.IsQuasiCompact (reduction X) ↔
      HasAffineEtaleCover X := sorry

/-- A formal algebraic space is quasi-compact when its reduction is a
quasi-compact algebraic space. -/
def IsQuasiCompact {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] : Prop :=
  ChosenBigFppfSite.IsQuasiCompact (reduction X)

namespace IsQuasiCompact

/-- An affine formal algebraic space over a size-closed chosen big fppf site
is quasi-compact. -/
theorem ofAffine {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    [Fact (ChosenBigSite.IsSizeClosed 𝒮)]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] : IsQuasiCompact X := sorry

/-- For a formal algebraic space over a size-closed chosen big fppf site,
quasi-compactness, quasi-compactness of its reduction, existence of a finite
étale affine atlas, and existence of an affine formal étale cover are equivalent. -/
theorem tfae {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    [Fact (ChosenBigSite.IsSizeClosed 𝒮)]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    List.TFAE [IsQuasiCompact X, ChosenBigFppfSite.IsQuasiCompact (reduction X),
      HasFiniteAffineEtaleAtlas X, HasAffineEtaleCover X] := sorry

end IsQuasiCompact

end AlgebraicGeometry.IsFormalAlgebraicSpace
