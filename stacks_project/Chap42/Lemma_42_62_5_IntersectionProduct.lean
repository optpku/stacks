/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Intersection.Diagonal
public import stacks_project.Chap42.Lemma_42_55_3_NormalClass

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ChowGroup AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules

universe u

/- The diagonal intersection product through its mathematical owner. -/
#check (AlgebraicGeometry.ChowGroup.intersectionProduct :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k)
    [LocallyOfFiniteType X.hom] {n m : ℤ} (r : ℕ)
    [IsFiniteLocallyFreeOfRank r (conormalSheaf (diagonal X).left)]
    (D : DiagonalSpecialization X r)
    (alpha : RelativeChow (fun _ ↦ 0) X n)
    (beta : RelativeChow (fun _ ↦ 0) X m),
    RelativeChow (fun _ ↦ 0) X (n + m - r))
