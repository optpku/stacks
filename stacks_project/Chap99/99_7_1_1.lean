/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Functor

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

universe u

/- 082N::statement_repair::1: the functor of quotients `Q_{F/X/B}` of a quasi-coherent `𝒪_X`-module `F`
along a morphism `f : X ⟶ B` of algebraic spaces over a scheme `S`. It sends a scheme
`T` over `B` to the set of quotients `F_T ⟶ Q` with `Q` quasi-coherent on
`X_T = X ×_B T` and flat over `T`, identifying quotients with the same kernel. -/
@[stacks 082N] #check (AlgebraicGeometry.AlgebraicSpace.Quot.functor :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) (F : X.Modules)
    [F.IsQuasicoherent], (SchemeOver B)ᵒᵖ ⥤ Type (u + 1))
