/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Functor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.FinitePresentation

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

/- Situation 99.7.1 (1): let `S` be a scheme, let `f : X ⟶ B` be a morphism of
algebraic spaces over `S`, and let `F` be a quasi-coherent `𝒪_X`-module. For a
scheme `T` over `B`, write `X_T = fiber f σ = X ×_B T` and write `F_T = fiberF f F σ`
for the pullback of `F` along the projection `X_T ⟶ X`. The functor of quotients
`Q_{F/X/B}` sends `T` to the set of kernel-identified quotients `F_T ⟶ Q` on
`X_T` with `Q` quasi-coherent and flat over `T`. -/
@[stacks 082M] #check (AlgebraicGeometry.AlgebraicSpace.Quot.functor :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) (F : X.Modules)
    [F.IsQuasicoherent], (SchemeOver B)ᵒᵖ ⥤ Type (u + 1))

/- Situation 99.7.1 (2): the finitely presented subfunctor `Q^{fp}_{F/X/B}` of
`Q_{F/X/B}` sends a scheme `T` over `B` to the subset of kernel-identified
quotients `F_T ⟶ Q` on `X_T` with `Q` quasi-coherent, flat over `T`, and of
finite presentation as an `𝒪_{X_T}`-module. -/
@[stacks 082M] #check (AlgebraicGeometry.AlgebraicSpace.Quot.fpFunctor :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) (F : X.Modules)
    [F.IsQuasicoherent], (SchemeOver B)ᵒᵖ ⥤ Type (u + 1))

/- Situation 99.7.1 (3): the inclusion `Q^{fp}_{F/X/B} ⟶ Q_{F/X/B}` is the
natural transformation `fpι` of functors `(Sch/B)ᵒᵖ ⥤ Sets`. -/
@[stacks 082M] #check (AlgebraicGeometry.AlgebraicSpace.Quot.fpι :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) (F : X.Modules)
    [F.IsQuasicoherent], AlgebraicGeometry.AlgebraicSpace.Quot.fpFunctor f F ⟶
      AlgebraicGeometry.AlgebraicSpace.Quot.functor f F)
