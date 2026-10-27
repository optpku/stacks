/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Intersection.Total

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules hiding dual

noncomputable section

universe u

open AlgebraicGeometry.ChowGroup

/- The fixed-rank diagonal intersection pairing on total Chow homology. -/
#check (AlgebraicGeometry.ChowGroup.Total.intersectionProduct :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k)
    [LocallyOfFiniteType X.hom] (r : ℕ)
    [IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)]
    (D : DiagonalSpecialization X r),
    Total (fun _ ↦ 0) X →+ Total (fun _ ↦ 0) X →+ Total (fun _ ↦ 0) X)
