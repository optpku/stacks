/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.FiniteDimensional
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/- Lemma 59.63.3 -/
@[stacks 0A3M] #check
  (AlgebraicGeometry.SchemeOverField.topCohomology_finiteDimensional :
    ∀ {k : Type u} [Field k]
      (X : AlgebraicGeometry.SchemeOverField k) [Algebraic X] [IsSeparated X.hom]
      [HasExt (Sheaf (Opens.grothendieckTopology X.left.carrier) AddCommGrpCat.{u})]
      (F : X.left.Modules) [F.IsCoherent] (d : ℕ),
      topologicalKrullDim X.left = (d : WithBot ℕ∞) →
        FiniteDimensional k (Scheme.Hom.cohomology X.hom F d))

end
