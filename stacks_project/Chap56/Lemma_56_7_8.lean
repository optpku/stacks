/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.ReconstructionOverField

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u

/- Lemma 56.7.8. A linear equivalence of coherent modules on finite-type schemes over a field,
with separated source and reduced target, is naturally isomorphic to pullback along an
isomorphism over the field followed by tensoring with an invertible module. -/
@[stacks 0FZR] #check
  (AlgebraicGeometry.Scheme.coherent_equivalence_pullback_tensor_invertible_over_field :
    ∀ {k : Type u} [Field k] {X Y : Scheme.{u}}
      (x : X ⟶ Spec (CommRingCat.of k)) (y : Y ⟶ Spec (CommRingCat.of k))
      [x.FiniteType] [y.FiniteType] [IsSeparated x] [IsReduced Y]
      (F : RingedSpace.Coh X.toRingedSpace ⥤ RingedSpace.Coh Y.toRingedSpace)
      [F.IsEquivalence] [LinearOverCoh x y F],
      ∃ (f : Y ≅ X) (L : Y.Modules),
        Scheme.Modules.Invertible L ∧
          f.hom ≫ x = y ∧
            Nonempty
              ((F ⋙ (SheafOfModules.isCoherent Y.toRingedSpace.ringCatSheaf).ι ⋙
                  Scheme.Modules.fromRingedSpace Y) ≅
                ((SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf).ι ⋙
                  Scheme.Modules.fromRingedSpace X ⋙
                  Scheme.Modules.pullback f.hom ⋙
                  CategoryTheory.MonoidalCategory.tensorRight L)))
