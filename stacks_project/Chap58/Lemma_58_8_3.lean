/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Thickening
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 58.8.3: for a thickening `i : X ⟶ X'`, base change induces an
equivalence between the categories of finite étale schemes over `X'` and `X`. -/
@[stacks 0BQB] #check
  (AlgebraicGeometry.Scheme.finiteEtaleBaseChangeIsEquivalenceOfThickening :
    ∀ {X X' : Scheme.{u}} (i : X ⟶ X') [IsThickening i],
      Functor.IsEquivalence (Scheme.finiteEtaleBaseChange i))

end AlgebraicGeometry.Scheme
