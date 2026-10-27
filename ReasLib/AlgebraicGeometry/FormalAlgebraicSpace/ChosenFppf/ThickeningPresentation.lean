/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.AlgebraicSpaceColimit
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.QuasiSeparated
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Reduction

/-!
# Thickening presentations of formal algebraic spaces

A quasi-compact quasi-separated formal algebraic space is isomorphic, as an
fppf sheaf, to a directed colimit of algebraic spaces along thickening
transitions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite
open AlgebraicGeometry.IsFormalAlgebraicSpace

noncomputable section

universe u v

namespace AlgebraicGeometry.IsFormalAlgebraicSpace

/-- A formal algebraic space with quasi-compact reduction and quasi-separated
affine tests is a nonempty directed colimit of algebraic spaces along relative
thickening transitions on a size-closed chosen big fppf site. -/
theorem exists_directedAlgebraicSpaceThickeningColimit
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    [Fact (ChosenBigSite.IsSizeClosed 𝒮)]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsQuasiSeparatedFormalAlgebraicSpace X]
    [ChosenBigFppfSite.IsQuasiCompact (reduction X)] :
    ∃ (Λ : Type (max u v)) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
      (D : Λ ⥤ Sheaf (𝒮.bigTopology S) (Type (max u v))),
        IsDirectedAlgebraicSpaceThickeningColimit D X := sorry

end AlgebraicGeometry.IsFormalAlgebraicSpace
