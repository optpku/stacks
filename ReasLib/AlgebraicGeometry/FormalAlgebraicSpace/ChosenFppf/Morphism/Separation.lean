/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChosenFppf.Morphism.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChosenFppf.Separation
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Basic

/-!
# Separated morphisms to formal algebraic spaces

Every morphism from a separated algebraic space to a formal algebraic space
on a chosen big fppf site is separated.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology

noncomputable section

universe u v

namespace AlgebraicGeometry.ChosenBigFppfSite.Separated

/-- Every morphism from a separated algebraic space to a formal algebraic
space on a chosen big fppf site is separated. -/
instance of_isSeparated {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {U X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsSeparated U] [IsFormalAlgebraicSpace X] (f : U ⟶ X) :
    Separated f := sorry

end AlgebraicGeometry.ChosenBigFppfSite.Separated
