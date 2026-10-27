/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Algebraic

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/- Lemma 97.18.1: A quotient stack is algebraic exactly when some restriction
has a saturation morphism that is a surjection of fppf sheaves and source and
target maps that are flat and locally of finite presentation. -/
@[stacks 06PJ] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.isAlgebraicStack_quotientStack_iff :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B),
      AlgebraicStack (SmallQuotient.quotientStack G) ↔
        ∃ (U' : Over B) (g : U' ⟶ G.U),
          Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
              (G.saturationMap g).left ∧
            Flat (G.pullback g) ∧ LocallyOfFinitePresentation (G.pullback g))

end AlgebraicGeometry.GroupoidAlgebraicSpace
