/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.VeryAmple.GenusBound

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme
open scoped MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/- Lemma 53.22.5: on a geometrically integral proper one-dimensional scheme over a
field with constant global functions, an invertible module of degree at least
`2 * genus X h_dimension hΓ + 1` is relatively very ample. -/
@[stacks 0H2V] #check
  (AlgebraicGeometry.SchemeOverField.relativelyVeryAmple_of_degreeBound :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
      [GeometricallyIntegral X.hom]
      (h_dimension : topologicalKrullDim X.left = 1)
      (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
      (L : X.left.Modules) [Scheme.Modules.Invertible L]
      (h_degree : 2 * (genus X h_dimension hΓ : ℤ) + 1 ≤
        Scheme.Modules.curveDegreeOfInvertible X.hom h_dimension.le L),
      RelativelyVeryAmple X.hom L)

end AlgebraicGeometry.SchemeOverField
