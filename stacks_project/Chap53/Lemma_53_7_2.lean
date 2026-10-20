/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.VeryAmple.DimensionOne
import StacksCheckRecall

open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SchemeOverField

/- Lemma 53.7.2: an ample, globally generated invertible module on a proper one-dimensional
scheme over a field, with constant global functions and vanishing first cohomology, has
relatively very ample second tensor power. -/
@[stacks 0E8W] #check
  (AlgebraicGeometry.SchemeOverField.relativelyVeryAmple_tensorPow_two :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
      (h_dimension : topologicalKrullDim X.left = 1)
      (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
      (L : X.left.Modules) [Scheme.Modules.Invertible L] [Scheme.Modules.IsAmple L]
      [SheafOfModules.IsGloballyGenerated L]
      (hH1 : IsZero (Scheme.Hom.cohomology X.hom L 1)),
      RelativelyVeryAmple X.hom (RingedSpace.TensorPower.sheaf L 2))

end AlgebraicGeometry.SchemeOverField
