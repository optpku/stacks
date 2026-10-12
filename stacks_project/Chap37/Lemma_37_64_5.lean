/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.Diagonal
import ReasLib.AlgebraicGeometry.Scheme.Morphism.WeaklyEtale.Composition
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 37.64.5 (1): flat diagonals are preserved by composition of scheme morphisms. -/
@[stacks 094T] #check
  (AlgebraicGeometry.Flat.diagonal_comp :
    ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      AlgebraicGeometry.Flat (pullback.diagonal f) →
        AlgebraicGeometry.Flat (pullback.diagonal g) →
          AlgebraicGeometry.Flat (pullback.diagonal (f ≫ g)))

/- Lemma 37.64.5 (2): weakly étale scheme morphisms are preserved by composition. -/
@[stacks 094T] #check
  (AlgebraicGeometry.WeaklyEtale.comp :
    ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      AlgebraicGeometry.WeaklyEtale f → AlgebraicGeometry.WeaklyEtale g →
        AlgebraicGeometry.WeaklyEtale (f ≫ g))
