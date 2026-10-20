/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Uniqueness
import StacksCheckRecall

open CategoryTheory
open scoped MonoidalCategory

universe u

/- Lemma 48.2.6 -/
@[stacks 0ATP] #check (AlgebraicGeometry.Scheme.IsDualizingComplex.existsInvertibleTensorIso :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X]
      [AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.toRingedSpace]
      [AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat.TensorDescends X.toRingedSpace]
      [AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat.IsLocalization X.toRingedSpace]
      {K K' : AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace},
      AlgebraicGeometry.Scheme.IsDualizingComplex K →
        AlgebraicGeometry.Scheme.IsDualizingComplex K' →
          ∃ L : AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace,
            CategoryTheory.MonoidalCategory.isInvertibleObject L ∧
              Nonempty (K' ≅ K ⊗ L))
