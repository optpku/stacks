/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDegree.BaseChange

open CategoryTheory Limits

universe u

/- Lemma 29.57.5: an arbitrary base change preserves a fixed bound on fibre degrees. -/
@[stacks 03J7] #check
  (AlgebraicGeometry.Scheme.Hom.degreesOfFibresBoundedBy_baseChange :
    ∀ {X Y Y' : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ Y) (g : Y' ⟶ Y) {n : ℕ},
      AlgebraicGeometry.Scheme.Hom.degreesOfFibresBoundedBy f n →
        AlgebraicGeometry.Scheme.Hom.degreesOfFibresBoundedBy (pullback.snd f g) n)

#check
  (AlgebraicGeometry.Scheme.Hom.universallyBoundedFibres_baseChange :
    ∀ {X Y Y' : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ Y) (g : Y' ⟶ Y),
      AlgebraicGeometry.Scheme.Hom.universallyBoundedFibres f →
        AlgebraicGeometry.Scheme.Hom.universallyBoundedFibres (pullback.snd f g))
