/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Filtered.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood.Decent

open CategoryTheory AlgebraicGeometry

universe u

@[expose] public section

namespace AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood.Elementary

/-- The category of elementary étale neighbourhoods of a point of a decent algebraic space is
cofiltered. -/
instance instIsCofiltered {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X] (x : Points X) :
    IsCofiltered (Elementary X x) := sorry

end AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood.Elementary
