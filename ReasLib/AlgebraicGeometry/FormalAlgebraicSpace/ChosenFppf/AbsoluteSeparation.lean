/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.ReductionSeparation

/-!
# Absolute separation of formal algebraic spaces
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology

noncomputable section

universe u v

namespace AlgebraicGeometry.IsFormalAlgebraicSpace

/-- A formal algebraic space is quasi-separated when its reduction is a
quasi-separated algebraic space. -/
def IsQuasiSeparated {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] : Prop :=
  ChosenBigFppfSite.IsQuasiSeparated (reduction X)

/-- A formal algebraic space is separated when its reduction is an absolutely
separated algebraic space. -/
def IsSeparated {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] : Prop :=
  ChosenBigFppfSite.IsSeparated (reduction X)

namespace IsQuasiSeparated

/-- An affine formal algebraic space over a size-closed chosen big fppf site
is quasi-separated. -/
theorem ofAffine {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [Fact (ChosenBigSite.IsSizeClosed 𝒮)]
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] : IsQuasiSeparated X := sorry

/-- A separated formal algebraic space over a size-closed chosen big fppf site
is quasi-separated. -/
theorem ofSeparated {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [Fact (ChosenBigSite.IsSizeClosed 𝒮)]
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] (h : IsSeparated X) : IsQuasiSeparated X := sorry

end IsQuasiSeparated

namespace IsSeparated

/-- An affine formal algebraic space over a size-closed chosen big fppf site
is separated. -/
theorem ofAffine {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [Fact (ChosenBigSite.IsSizeClosed 𝒮)]
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] : IsSeparated X := sorry

/-- Over a size-closed chosen big fppf site, separatedness of the reduction
of a formal algebraic space is equivalent to the separated formal algebraic
space condition defined by affine pullback tests. -/
theorem iff_isSeparatedFormalAlgebraicSpace
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [Fact (ChosenBigSite.IsSizeClosed 𝒮)]
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    IsSeparated X ↔ AlgebraicGeometry.IsSeparatedFormalAlgebraicSpace X := sorry

end IsSeparated

end AlgebraicGeometry.IsFormalAlgebraicSpace
