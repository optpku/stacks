/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.FunctorExtension
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Reconstruction

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- A coherent-module equivalence on Noetherian schemes is induced by pullback
along a scheme isomorphism followed by tensoring with an invertible module. -/
theorem coherent_equivalence_pullback_tensor_invertible
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (F : RingedSpace.Coh X.toRingedSpace ⥤ RingedSpace.Coh Y.toRingedSpace)
    [F.IsEquivalence] :
    ∃ (f : Y ≅ X) (L : Y.Modules),
      Scheme.Modules.Invertible L ∧
        ∀ 𝓕 : RingedSpace.Coh X.toRingedSpace,
          Nonempty ((F.obj 𝓕).obj ≅
            (CategoryTheory.MonoidalCategory.tensorRight L).obj
              ((Scheme.Modules.pullback f.hom).obj 𝓕.obj)) := sorry

end AlgebraicGeometry.Scheme
