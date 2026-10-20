/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.FinitePresentation
public import stacks_project.Chap99.«99_7_1_1_Functor»

/-!
# The functor of finitely presented quotients

The finitely presented quotient functor is imported from its mathematical owner.
The general quotient import retains the source-facing category abbreviation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Quot.fpFunctor :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) (F : X.Modules)
    [F.IsQuasicoherent], (SchemeOver B)ᵒᵖ ⥤ Type (u + 1))
