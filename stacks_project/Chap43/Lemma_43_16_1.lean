/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.IntersectionMultiplicity.CohenMacaulay

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open TopCat.Presheaf
open scoped AlgebraicGeometry

noncomputable section

universe u

variable {k : Type u} [Field k] (X : SchemeOverField k) [Variety X]
  [Scheme.Regular X.left] (V W : X.left.IdealSheafData)
  [IsIntegral V.subscheme] [IsIntegral W.subscheme]

/- Lemma 43.16.1 (1): at a component where both closed subvarieties are
Cohen–Macaulay, their Serre intersection multiplicity is the local length of the
scheme-theoretic intersection. -/
@[stacks 0B02] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.intersectionMultiplicity_eq_componentMultiplicity_of_cohenMacaulay
      X V W :
    ∀ (hproper : Closeds.IntersectProperly V.support W.support)
      (Z : irreducibleComponents (V ⊔ W).subscheme)
      [hV : CohenMacaulayRing
        (stalk V.subscheme.presheaf
          ((Scheme.IdealSheafData.inclusion (le_sup_left : V ≤ V ⊔ W)).base
            (genericPoints.ofComponent Z).1) : CommRingCat)]
      [hW : CohenMacaulayRing
        (stalk W.subscheme.presheaf
          ((Scheme.IdealSheafData.inclusion (le_sup_right : W ≤ V ⊔ W)).base
            (genericPoints.ofComponent Z).1) : CommRingCat)],
      V.intersectionMultiplicity W (genericPoints.ofComponent Z) =
        ((V ⊔ W).componentMultiplicity (genericPoints.ofComponent Z) : ℤ))

/- Lemma 43.16.1 (2): if both properly intersecting closed subvarieties are
Cohen–Macaulay, their intersection cycle is the expected-dimensional associated cycle
of their scheme-theoretic intersection. -/
@[stacks 0B02] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.intersectionCycle_eq_associatedCycle_of_cohenMacaulay
      X V W :
    ∀ [Scheme.CohenMacaulay V.subscheme] [Scheme.CohenMacaulay W.subscheme]
      (hproper : Closeds.IntersectProperly V.support W.support),
      AlgebraicGeometry.Scheme.IdealSheafData.intersectionCycle V W hproper =
        ((V ⊔ W).associatedCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0))
          (AlgebraicGeometry.Scheme.IdealSheafData.expectedIntersectionDimension X V W) :
            AlgebraicCycle X.left ℤ))
