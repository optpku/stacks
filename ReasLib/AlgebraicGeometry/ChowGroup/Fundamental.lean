/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Additive
public import ReasLib.AlgebraicGeometry.CycleGroup.Fundamental
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Modification

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

/-- The Chow class represented by the degree-`k` fundamental cycle. -/
noncomputable def fundamentalClass {Z : Scheme.{u}} [IsLocallyNoetherian Z]
    (d : Z → ℤ) [IsDimensionFunction d] (k : ℤ) : ChowGroup Z d k :=
  chowClass d k (CycleGroup.fundamental d k)

end AlgebraicGeometry.ChowGroup
