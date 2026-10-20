/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Inclusion

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite

noncomputable section

universe u

/- Situation 99.8.1 (1): let `S` be a scheme, let `f : X ⟶ B` be a morphism of
finite presentation of algebraic spaces over `S`, and let `F` be a quasi-coherent
`𝒪_X`-module. For a scheme `T` over `B`, write `X_T = X ×_B T` and write `F_T`
for the pullback of `F` along the projection `X_T ⟶ X`. The Quot functor
`Quot_{F/X/B}` sends `T` to the set of kernel-identified quotients `F_T ⟶ Q`
on `X_T` with `Q` quasi-coherent of finite presentation, flat over `T`, and with
support proper over `T`. -/
@[stacks 09TR] #check (AlgebraicGeometry.AlgebraicSpace.Quot.quot :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent], (SchemeOver B)ᵒᵖ ⥤ Type (u + 1))

/- Situation 99.8.1 (2): by Derived Categories of Spaces, Lemma 75.7.8, the
Quot functor `Quot_{F/X/B}` is a subfunctor of `Q^{fp}_{F/X/B}`. -/
@[stacks 09TR] #check (AlgebraicGeometry.AlgebraicSpace.Quot.quotFpι :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent],
    AlgebraicGeometry.AlgebraicSpace.Quot.quot f F ⟶
      AlgebraicGeometry.AlgebraicSpace.Quot.fpFunctor f F)

#check (AlgebraicGeometry.AlgebraicSpace.Quot.quotFpι_app_injective :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f]
    (F : X.Modules) [F.IsQuasicoherent] (σ : (SchemeOver B)ᵒᵖ),
    Function.Injective ((AlgebraicGeometry.AlgebraicSpace.Quot.quotFpι f F).app σ))

