/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HomFunctor

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

/- Situation 99.3.1: let `S` be a scheme, let `f : X ⟶ B` be a morphism of
algebraic spaces over `S`, and let `F`, `G` be quasi-coherent `𝒪_X`-modules.
For a scheme `T` over `B`, write `X_T = baseChangeSpace f σ.hom = X ×_B T`
and write `F_T = baseChangeModule f σ.hom F`,
`G_T = baseChangeModule f σ.hom G` for the pullbacks of `F` and `G` along
the projection `baseChangeProj : X_T ⟶ X`. The Hom functor
`Hom(F, G) : (SchemeOver B)ᵒᵖ ⥤ Sets` sends `T` to
`Hom_{𝒪_{X_T}}(F_T, G_T)`. -/
@[stacks 08JT] #check (AlgebraicGeometry.AlgebraicSpace.Modules.homFunctor :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) (F G : X.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent], (SchemeOver B)ᵒᵖ ⥤ Type (u + 1))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.homFunctor_obj :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) (F G : X.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] (σ : SchemeOver B),
    (AlgebraicGeometry.AlgebraicSpace.Modules.homFunctor f F G).obj (op σ) =
      (AlgebraicGeometry.AlgebraicSpace.Modules.baseChangeModule f σ.hom F ⟶
        AlgebraicGeometry.AlgebraicSpace.Modules.baseChangeModule f σ.hom G))
