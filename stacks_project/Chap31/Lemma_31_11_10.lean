/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Torsion.AssociatedPoints

universe u

/- Lemma 31.11.10: for a nonzero coherent module on a locally Noetherian integral scheme,
torsion-freeness, having only the generic associated point, support together with Serre's
condition `(S_1)`, and support together with no embedded associated points are equivalent. -/
@[stacks 0AXY] #check
  (AlgebraicGeometry.Scheme.Modules.IsTorsionFree.tfae_associatedPoints_support_serreS1 :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X]
      [AlgebraicGeometry.IsLocallyNoetherian X] (ℱ : X.Modules) [ℱ.IsCoherent]
      (_ : ¬ CategoryTheory.Limits.IsZero ℱ), List.TFAE
        [ AlgebraicGeometry.Scheme.Modules.IsTorsionFree ℱ,
          AlgebraicGeometry.Scheme.Modules.associatedPoints ℱ = ({genericPoint X} : Set X),
          genericPoint X ∈ AlgebraicGeometry.RingedSpace.moduleSupport ℱ ∧
            AlgebraicGeometry.Scheme.Modules.satisfiesSerreConditionS ℱ 1,
          genericPoint X ∈ AlgebraicGeometry.RingedSpace.moduleSupport ℱ ∧
            AlgebraicGeometry.Scheme.Modules.embeddedAssociatedPoints ℱ = (∅ : Set X) ])
