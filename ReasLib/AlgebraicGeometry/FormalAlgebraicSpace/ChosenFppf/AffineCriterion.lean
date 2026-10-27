/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChosenFppf.Affine
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Reduction

/-!
# Affineness of formal algebraic spaces and their reductions

A formal algebraic space is an affine formal algebraic space if and only if
its reduction is an affine algebraic space.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite
open AlgebraicGeometry.IsFormalAlgebraicSpace

noncomputable section

universe u v

namespace AlgebraicGeometry.IsFormalAlgebraicSpace

/-- A formal algebraic space on a size-closed chosen big fppf site is affine
formal if and only if its canonical reduction is an affine algebraic space. -/
theorem isAffineFormalAlgebraicSpace_iff_isAffine_reduction
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    [Fact (ChosenBigSite.IsSizeClosed 𝒮)]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    IsAffineFormalAlgebraicSpace X ↔ ChosenBigFppfSite.IsAffine (reduction X) := sorry

end AlgebraicGeometry.IsFormalAlgebraicSpace
