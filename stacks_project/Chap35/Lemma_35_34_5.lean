/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.DescentData.Coproduct
import StacksCheckRecall

open CategoryTheory

universe u v

/- Lemma 35.34.5: Descent data for a small family of scheme morphisms are canonically equivalent
to descent data for the induced morphism from the coproduct of their sources. -/
@[stacks 023X] #check (AlgebraicGeometry.Scheme.DescentData.coproductEquivalence :
    ∀ {I : Type v} [Small.{u} I] {S : AlgebraicGeometry.Scheme.{u}}
      (X : I → AlgebraicGeometry.Scheme.{u}) (f : ∀ i, X i ⟶ S),
      AlgebraicGeometry.Scheme.DescentData X f ≌
        AlgebraicGeometry.Scheme.DescentData
          (AlgebraicGeometry.Scheme.DescentData.coproductFamily X)
          (AlgebraicGeometry.Scheme.DescentData.coproductArrow X f))
