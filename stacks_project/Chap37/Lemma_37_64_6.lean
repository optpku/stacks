/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat.Diagonal.BaseChange
import ReasLib.AlgebraicGeometry.Scheme.Morphism.WeaklyEtale.BaseChange
import StacksCheckRecall

universe u

/- Lemma 37.64.6 (1): base change preserves flatness of the diagonal morphism. -/
@[stacks 094U] #check
  (AlgebraicGeometry.Flat.diagonal_baseChange :
    ∀ {X Y Y' : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y),
      AlgebraicGeometry.Flat (CategoryTheory.Limits.pullback.diagonal f) →
        AlgebraicGeometry.Flat
          (CategoryTheory.Limits.pullback.diagonal
            (CategoryTheory.Limits.pullback.fst g f)))

/- Lemma 37.64.6 (2): base change preserves weakly étale scheme morphisms. -/
@[stacks 094U] #check
  (AlgebraicGeometry.WeaklyEtale.baseChange :
    ∀ {X Y Y' : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y),
      AlgebraicGeometry.WeaklyEtale f →
        AlgebraicGeometry.WeaklyEtale (CategoryTheory.Limits.pullback.fst g f))
