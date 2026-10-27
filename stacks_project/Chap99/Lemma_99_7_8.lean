/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Quot.Pushout

/-!
# Lemma 99.7.8

In Situation 99.7.1, a pushout square of schemes over `B` where `Z ⟶ Z'`
is a thickening and `Z ⟶ Y` is affine induces a bijective
restriction map on `functor f F` and, if `X ⟶ B` is locally of finite
presentation, on `fpFunctor f F`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite
open AlgebraicGeometry.AlgebraicSpace.Quot

noncomputable section

universe u

/- Lemma 99.7.8 (1): in Situation 99.7.1, for a pushout square of schemes over
`B` where `Z ⟶ Z'` is a thickening and `Z ⟶ Y` is affine, the natural map
`FunctorToTypes.pushoutComparison (functor f F) H.w` is bijective. -/
@[stacks 08IW] #check (AlgebraicGeometry.AlgebraicSpace.Quot.pushoutComparison_bijective :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {Z Z' Y Y' : SchemeOver B} (i : Z ⟶ Z') (g : Z ⟶ Y)
    (inl : Z' ⟶ Y') (inr : Y ⟶ Y')
    [IsThickening i.left.left] [IsAffineHom g.left.left]
    (H : IsPushout i g inl inr),
    Function.Bijective (FunctorToTypes.pushoutComparison (functor f F) H.w))

/- Lemma 99.7.8 (2): in Situation 99.7.1, if `X ⟶ B` is locally of finite
presentation, then the same comparison is bijective for `fpFunctor f F`. -/
@[stacks 08IW] #check (AlgebraicGeometry.AlgebraicSpace.Quot.fpPushoutComparison_bijective :
  ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) [LocallyOfFinitePresentation f] (F : X.Modules)
    [F.IsQuasicoherent] {Z Z' Y Y' : SchemeOver B} (i : Z ⟶ Z') (g : Z ⟶ Y)
    (inl : Z' ⟶ Y') (inr : Y ⟶ Y')
    [IsThickening i.left.left] [IsAffineHom g.left.left]
    (H : IsPushout i g inl inr),
    Function.Bijective (FunctorToTypes.pushoutComparison (fpFunctor f F) H.w))
