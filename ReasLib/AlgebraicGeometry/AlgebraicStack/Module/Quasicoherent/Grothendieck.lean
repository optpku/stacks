/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Abelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh

/-- Quasi-coherent modules on an algebraic stack form a Grothendieck abelian category
relative to the universe of their sections. -/
instance instIsGrothendieckAbelian {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    IsGrothendieckAbelian.{u} (QCoh X) :=
  sorry

/-- The inclusion of quasi-coherent modules into all module sheaves on an algebraic stack
has a right adjoint. -/
instance inclusionIsLeftAdjoint {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    (inclusion X).IsLeftAdjoint :=
  sorry

end AlgebraicGeometry.GroupoidsOver.QCoh
