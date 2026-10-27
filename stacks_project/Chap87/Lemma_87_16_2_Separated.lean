/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChosenFppf.Separation

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.ChosenBigFppfSite

universe u v

/- Absolute separatedness of an algebraic-space sheaf is characterized by its
affine pullbacks and their canonical section tensor maps. -/
#check (AlgebraicGeometry.ChosenBigFppfSite.IsSeparated.iff :
  ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier},
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))] →
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))] →
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) →
    (ChosenBigFppfSite.IsSeparated X ↔
      IsAlgebraicSpace X ∧ forallAffinePullbackAffineSurjective X))
