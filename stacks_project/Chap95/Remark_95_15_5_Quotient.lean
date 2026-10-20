/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.QuotientStack.AbstractGroup

open CategoryTheory AlgebraicGeometry

universe u

/- The quotient stack of an algebraic space by a small abstract group action. -/
#check (AlgebraicGeometry.QuotientStack.AbstractGroup.stack :
  ∀ {S : Scheme.{u}} {G : Type u} [Group G] {X : AlgebraicSpace S}
    (_ρ : G →* Aut X), StackOver.Groupoids (Scheme.fppfTopology.over S))
