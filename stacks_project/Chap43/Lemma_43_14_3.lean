/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.IntersectionMultiplicity

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open Scheme.IdealSheafData
open scoped AlgebraicGeometry

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : AlgebraicGeometry.SchemeOverField k) [Variety X]
  [Scheme.Regular X.left] (V W : X.left.IdealSheafData)
  [Variety (Over.mk (V.subschemeι ≫ X.hom))]
  [Variety (Over.mk (W.subschemeι ≫ X.hom))]

/- Lemma 43.14.3 (1): a multiplicity-one component of the proper intersection of two
closed subvarieties in a nonsingular variety has intersection multiplicity one. -/
@[stacks 0B1I] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.intersectionMultiplicity_eq_one_of_componentMultiplicity_eq_one
      X V W :
    (hproper : Closeds.IntersectProperly V.support W.support) →
    (ξ : genericPoints (V ⊔ W).subscheme) →
    componentMultiplicity (V ⊔ W) ξ = 1 →
    V.intersectionMultiplicity W ξ = 1)

/- Lemma 43.14.3 (2): the left closed subvariety is smooth at the generic point of a
multiplicity-one component of the proper intersection. -/
@[stacks 0B1I] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.leftSmoothAt_of_componentMultiplicity_eq_one
      X V W :
    (hproper : Closeds.IntersectProperly V.support W.support) →
    (ξ : genericPoints (V ⊔ W).subscheme) →
    componentMultiplicity (V ⊔ W) ξ = 1 →
    (V.subschemeι ≫ X.hom).SmoothAt
      ((inclusion (le_sup_left : V ≤ V ⊔ W)).base ξ.1))

/- Lemma 43.14.3 (3): the right closed subvariety is smooth at the generic point of a
multiplicity-one component of the proper intersection. -/
@[stacks 0B1I] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.rightSmoothAt_of_componentMultiplicity_eq_one
      X V W :
    (hproper : Closeds.IntersectProperly V.support W.support) →
    (ξ : genericPoints (V ⊔ W).subscheme) →
    componentMultiplicity (V ⊔ W) ξ = 1 →
    (W.subschemeι ≫ X.hom).SmoothAt
      ((inclusion (le_sup_right : W ≤ V ⊔ W)).base ξ.1))
