/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.VirtualNormalBundle

open AlgebraicGeometry CategoryTheory

universe u

#check (AlgebraicGeometry.Scheme.Hom.VirtualNormalBundle :
  ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i], Type (u + 1))
