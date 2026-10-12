/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.Perfect

@[expose] public section

open CategoryTheory

universe u

open AlgebraicGeometry

#check (AlgebraicGeometry.IsKoszulRegularImmersion.isPerfect :
  ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsKoszulRegularImmersion i],
    LocallyOfType RingHom.IsPerfectRingMap i)
