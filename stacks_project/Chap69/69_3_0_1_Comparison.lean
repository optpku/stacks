/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HigherDirectImage.EtaleBaseChange

/-! # Compatibility checks for étale higher-direct-image base change -/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Functor.RightDerived` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImageEtaleBaseChangeHom`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

#check (AlgebraicGeometry.AlgebraicSpace.Modules.higherDirectImageEtaleBaseChangeNatTrans :
    ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
      {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (h_cart : IsPullback h f' f g)
    [Etale g] [Etale h]
    [Abelian X.Modules] [Abelian X'.Modules] [Abelian Y.Modules] [Abelian Y'.Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions X'.Modules] (i : ℕ),
    higherDirectImageFunctor f i ⋙ restrictFunctor g ⟶
      restrictFunctor h ⋙ higherDirectImageFunctor f' i)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.higherDirectImageEtaleBaseChangeHom :
    ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
      {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (h_cart : IsPullback h f' f g)
    [Etale g] [Etale h]
    [Abelian X.Modules] [Abelian X'.Modules] [Abelian Y.Modules] [Abelian Y'.Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions X'.Modules]
    (F : X.Modules) (i : ℕ),
    (restrictFunctor g).obj (higherDirectImage f F i) ⟶
      higherDirectImage f' (restrict F h) i)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.higherDirectImageEtaleBaseChangeIso :
    ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
      {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (h_cart : IsPullback h f' f g)
    [Etale g] [Etale h]
    [Abelian X.Modules] [Abelian X'.Modules] [Abelian Y.Modules] [Abelian Y'.Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions X'.Modules]
    (F : X.Modules) (i : ℕ),
    (restrictFunctor g).obj (higherDirectImage f F i) ≅
      higherDirectImage f' (restrict F h) i)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.higherDirectImageEtaleBaseChangeIso_hom :
    ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
      {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (h_cart : IsPullback h f' f g)
    [Etale g] [Etale h]
    [Abelian X.Modules] [Abelian X'.Modules] [Abelian Y.Modules] [Abelian Y'.Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions X'.Modules]
    (F : X.Modules) (i : ℕ),
    (higherDirectImageEtaleBaseChangeIso h_cart F i).hom =
      higherDirectImageEtaleBaseChangeHom h_cart F i)
