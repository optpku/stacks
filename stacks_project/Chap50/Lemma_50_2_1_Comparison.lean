/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Differentials.ExteriorPower.BaseChange

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

#check (AlgebraicGeometry.Scheme.RelativeDifferentials.formComparison :
  ∀ {X' X S' S : Scheme.{u}}
    {f : X' ⟶ X} {g : S' ⟶ S} {h : X ⟶ S} {h' : X' ⟶ S'},
    CommSq f h' h g → ∀ p : ℕ,
      (RingedSpace.Hom.pullback f.toShHom).obj (Λ[p] Ω[h.toShHom]) ⟶
        Λ[p] Ω[h'.toShHom])
