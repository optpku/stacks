/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.AffineCriterion
import StacksCheckRecall

universe u

/- Lemma 30.3.1: A quasi-compact scheme is affine if first cohomology vanishes for every
quasi-coherent ideal sheaf. -/
@[stacks 01XF] #check
  (AlgebraicGeometry.Scheme.isAffine_of_H1_vanishes_for_quasiCoherent_idealSheaves :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [CompactSpace X.carrier],
      (∀ I : AlgebraicGeometry.Scheme.IdealSubobject X,
        I.toModule.IsQuasicoherent →
          CategoryTheory.Limits.IsZero
            (((SheafOfModules.toSheaf X.ringCatSheaf).obj I.toModule).H' 1
              (⊤ : X.Opens))) →
        AlgebraicGeometry.IsAffine X)
