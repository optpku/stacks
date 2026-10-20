/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FreeQuotient

/-!
# Free abstract-group quotients of algebraic spaces

This module records the pointwise action of an abstract group homomorphism
`ρ : G →* Aut X` on the functor of points of an algebraic space, the orbit
presheaf `T ↦ X(T)/G`, and the associated fppf quotient sheaf.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.AlgebraicSpace.IsFree :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {G : Type u} [Group G],
    (G →* Aut X) → Prop)
