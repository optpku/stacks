/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallyEtale.Composition
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 37.8.3: A composition of formally étale morphisms is formally étale. -/
@[stacks 02HI] #check
  (@AlgebraicGeometry.FormallyEtale.comp :
    ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
      [AlgebraicGeometry.FormallyEtale f] [AlgebraicGeometry.FormallyEtale g],
      AlgebraicGeometry.FormallyEtale (f ≫ g))
