/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import stacks_project.Chap53.Lemma_53_22_2
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.GlobalGeneration

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme
open scoped MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/- Lemma 53.22.3: under Situation 53.6.2, an invertible module on an integral
proper curve whose degree is at least twice the genus is globally generated. -/
@[stacks 0E3C] #check
  (AlgebraicGeometry.SchemeOverField.isGloballyGenerated_of_curveDegree_ge_two_mul_genus :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
      [IsIntegral X.left]
      (h_dimension : topologicalKrullDim X.left = 1)
      (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
      (L : X.left.Modules) [Scheme.Modules.Invertible L]
      (h_degree : 2 * (genus X h_dimension hΓ : ℤ) ≤
        Scheme.Modules.curveDegreeOfInvertible X.hom h_dimension.le L),
      SheafOfModules.IsGloballyGenerated L)

end AlgebraicGeometry.SchemeOverField
