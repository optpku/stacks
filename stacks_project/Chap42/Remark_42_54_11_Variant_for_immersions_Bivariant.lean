/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.VirtualNormalBundle

open AlgebraicGeometry CategoryTheory

universe u

#check (AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle.CompletedClass :
  ∀ {S Z X : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (q : Z ⟶ S) (p : X ⟶ S)
    [LocallyOfFiniteType q] [LocallyOfFiniteType p]
    (i : Z ⟶ X) (hi : i ≫ p = q) [IsImmersion i]
    (V : AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle i), Type (u + 1))
