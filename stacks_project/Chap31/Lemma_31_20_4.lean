/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.Ideal.QuasiRegular
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 31.20.4: an ideal sheaf on a locally ringed space is quasi-regular if and only if it is
of finite type, its conormal module is finite locally free, and all canonical symmetric-power
maps to the associated-graded pieces are isomorphisms. -/
@[stacks 063H] #check
  (AlgebraicGeometry.LocallyRingedSpace.isQuasiRegularIdealSheaf_iff :
    ∀ {X : AlgebraicGeometry.LocallyRingedSpace.{u}}
      (I : AlgebraicGeometry.LocallyRingedSpace.IdealSubobject X),
      AlgebraicGeometry.RingedSpace.IsQuasiRegularIdealSheaf I ↔
        I.toModule.IsFiniteType ∧
          AlgebraicGeometry.RingedSpace.idealSheafConormalFiniteLocallyFreeCriterion I ∧
            AlgebraicGeometry.RingedSpace.idealSheafAssociatedGradedPolynomialCriterion I)
