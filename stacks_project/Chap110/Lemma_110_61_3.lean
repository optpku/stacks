/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Derived.Pushforward.NonPreservation
import StacksCheckRecall

/-! # Derived pushforward of quasi-coherent modules need not exist unbounded -/

@[expose] public section

open AlgebraicGeometry CategoryTheory AlgebraicStack GroupoidsOver
open scoped Bicategory

universe u

/- Lemma 110.61.3: a quasi-compact quasi-separated morphism of algebraic stacks
need not induce unbounded derived pushforward on quasi-coherent modules. -/
@[stacks 07DD] #check (AlgebraicGeometry.AlgebraicStack.not_forall_mapsDerivedLQCohFbc :
  ¬ ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
      [QuasiCompact f] [QuasiSeparated f], mapsDerivedLQCohFbc f)
