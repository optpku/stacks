/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.DeligneMumford
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 94.12.2: an algebraic stack `X` over a scheme `S` contained in
`Sch_fppf` is a Deligne-Mumford stack if there exists a scheme `U` over `S`
and a surjective étale 1-morphism `slice U ⟶ X`. -/
@[stacks 03YO] #check (AlgebraicGeometry.DeligneMumfordStack :
  ∀ {S : Scheme.{u}}, AlgebraicGeometry.GroupoidsOver S → Prop)
