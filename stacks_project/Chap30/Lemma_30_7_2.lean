/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.BaseChange

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.OpenCoverCech

variable {X S S' : Scheme.{u}} {ι : Type u}

/- Lemma 30.7.2
For a finite affine open cover, pulling its pushed-forward Čech complex through an arbitrary
scheme base change gives the bounded-below derived pushforward of the base-changed module.
-/
@[stacks 01XM] #check
  (derivedBaseChange_isomorphic :
    ∀ {X S S' : Scheme.{u}} {ι : Type u}
      (f : X ⟶ S) (g : S' ⟶ S)
      [IsAffineHom (pullback.diagonal (terminal.from X))]
      [IsAffineHom (pullback.diagonal (terminal.from S))]
      [Finite ι]
      (𝒰 : ι → X.Opens) (h𝒰 : IsOpenCover 𝒰)
      (h𝒰_affine : ∀ i, IsAffineOpen (𝒰 i))
      (ℱ : X.Modules) [ℱ.IsQuasicoherent],
    IsIsomorphic
      (DerivedCategory.Plus.Qh.obj
        ((HomotopyCategory.Plus.quotient S'.Modules).obj
          (((Scheme.Modules.pullback g).mapCochainComplexPlus).obj
            ((CochainComplex.Plus.extendNat S.Modules).obj
              (pushforward f 𝒰 ℱ)))))
      ((Scheme.Modules.pushforward (pullback.snd f g)).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor (pullback f g : Scheme.{u}).Modules 0).obj
          (Scheme.Modules.baseChangeModule f g ℱ))))

#check
  (baseChange_isomorphic :
    ∀ {X S S' : Scheme.{u}} {ι : Type u}
      (f : X ⟶ S) (g : S' ⟶ S)
      [IsAffineHom (pullback.diagonal (terminal.from X))]
      [IsAffineHom (pullback.diagonal (terminal.from S))]
      [Finite ι]
      (𝒰 : ι → X.Opens) (h𝒰 : IsOpenCover 𝒰)
      (h𝒰_affine : ∀ i, IsAffineOpen (𝒰 i))
      (ℱ : X.Modules) [ℱ.IsQuasicoherent],
    IsIsomorphic
      (((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (pushforward f 𝒰 ℱ))
      (pushforward (pullback.snd f g)
        (baseChangeOpenFamily f g 𝒰)
        (Scheme.Modules.baseChangeModule f g ℱ)))

#check
  (AlgebraicGeometry.Scheme.isOpenCover_baseChangeOpenFamily :
    ∀ {X S S' : Scheme.{u}} {ι : Type u}
      (f : X ⟶ S) (g : S' ⟶ S)
      (𝒰 : ι → X.Opens) (h𝒰 : IsOpenCover 𝒰),
      IsOpenCover (baseChangeOpenFamily f g 𝒰))

#check
  (AlgebraicGeometry.Scheme.isAffineOpen_baseChangeOpenFamily_of_isAffineHom :
    ∀ {X S S' : Scheme.{u}} {ι : Type u}
      (f : X ⟶ S) (g : S' ⟶ S) [IsAffineHom g]
      (𝒰 : ι → X.Opens) (h𝒰_affine : ∀ i, IsAffineOpen (𝒰 i)),
      ∀ i, IsAffineOpen (baseChangeOpenFamily f g 𝒰 i))

end AlgebraicGeometry.Scheme.OpenCoverCech
