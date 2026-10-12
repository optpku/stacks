/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection.Composition
import StacksCheckRecall

open CategoryTheory

universe u

/-
Lemma 37.62.7

A composition of local complete intersection morphisms is a local complete intersection morphism.
-/
@[stacks 069J] #check
  (AlgebraicGeometry.LocallyOfType.isLocalCompleteIntersection_comp :
    ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
      [AlgebraicGeometry.LocallyOfType RingHom.IsLocalCompleteIntersection f]
      [AlgebraicGeometry.LocallyOfType RingHom.IsLocalCompleteIntersection g],
      AlgebraicGeometry.LocallyOfType RingHom.IsLocalCompleteIntersection (f ≫ g))
