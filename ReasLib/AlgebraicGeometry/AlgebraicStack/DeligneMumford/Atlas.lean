/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.DeligneMumford
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Unramified

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.DeligneMumfordStack

/-- A surjective, flat, locally finitely presented, unramified morphism from an
algebraic space to an algebraic stack exhibits the target as a Deligne-Mumford
stack. -/
theorem of_unramified {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    {W : AlgebraicSpace S} (f : W.toGroupoids ⟶ X)
    [Groupoids.Hom.Surjective f] [Groupoids.Hom.Flat f]
    [Groupoids.Hom.LocallyOfFinitePresentation f]
    (h_unramified : Groupoids.Hom.has (@AlgebraicSpace.Unramified S) f) :
    DeligneMumfordStack X :=
  sorry

end AlgebraicGeometry.DeligneMumfordStack
