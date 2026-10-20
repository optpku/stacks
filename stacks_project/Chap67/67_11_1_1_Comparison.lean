/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.EtaleBaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.DirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.EtaleBaseChange

/-! # Canonical module comparison for étale cartesian squares -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Modules.pushforwardEtaleBaseChangeNatTrans :
  ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (h_cart : IsPullback h f' f g) [Etale g] [Etale h],
    pushforward f ⋙ restrictFunctor g ⟶ restrictFunctor h ⋙ pushforward f')

#check (AlgebraicGeometry.AlgebraicSpace.Modules.pushforwardEtaleBaseChangeHom :
  ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (h_cart : IsPullback h f' f g) [Etale g] [Etale h] (F : X.Modules),
    (restrictFunctor g).obj ((pushforward f).obj F) ⟶
      (pushforward f').obj ((restrictFunctor h).obj F))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.pushforwardEtaleBaseChangeHom_eq :
  ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (h_cart : IsPullback h f' f g) [Etale g] [Etale h] (F : X.Modules),
    pushforwardEtaleBaseChangeHom h_cart F =
      (AlgebraicGeometry.AlgebraicSpace.Modules.pushforwardEtaleBaseChangeNatTrans h_cart).app F)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.isIso_pushforwardEtaleBaseChangeHom :
  ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (h_cart : IsPullback h f' f g) [Etale g] [Etale h] (F : X.Modules),
    IsIso (pushforwardEtaleBaseChangeHom h_cart F))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.pushforwardEtaleBaseChangeIso :
  ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (h_cart : IsPullback h f' f g) [Etale g] [Etale h] (F : X.Modules),
    (restrictFunctor g).obj ((pushforward f).obj F) ≅
      (pushforward f').obj ((restrictFunctor h).obj F))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.pushforwardEtaleBaseChangeIso_hom :
  ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (h_cart : IsPullback h f' f g) [Etale g] [Etale h] (F : X.Modules),
    (pushforwardEtaleBaseChangeIso h_cart F).hom =
      pushforwardEtaleBaseChangeHom h_cart F)
