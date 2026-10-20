/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Impurity.FinitePresentation
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 38.15.3: if `F` has an impurity above `s`, then it has one whose base-change
morphism is locally of finite presentation and whose special point is closed in its fibre. -/
@[stacks 05FX]
#check
  (AlgebraicGeometry.Scheme.Modules.Impurity.exists_locallyOfFinitePresentation_closedPoint :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (F : X.Modules) (f : X ⟶ S)
        [AlgebraicGeometry.Scheme.Hom.FiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]
        (s : S),
      Nonempty (AlgebraicGeometry.Scheme.Modules.Impurity F f s) →
        ∃ I : AlgebraicGeometry.Scheme.Modules.Impurity F f s,
          AlgebraicGeometry.LocallyOfFinitePresentation I.g ∧
            I.g.asFiber I.specialPoint ∈
              closedPoints (I.g.fiber (I.g I.specialPoint)))
