/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.EtaleBaseChange

/-!
# Étale base change for derived pushforward of modules

A cartesian square of algebraic spaces with étale vertical edges induces the canonical
identification between derived pushforward followed by restriction and restriction followed
by derived pushforward.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits CategoryTheory.Functor
open ComplexShape

noncomputable section

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Modules.derivedPushforwardRestrictCompositeUnit :
  ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    [Etale g] [Etale h],
    modulesMapHomotopy (pushforward f) ⋙ modulesHomotopyToDerived (restrictFunctor g) ⟶
      modulesQh X ⋙ modulesHomotopyFunctor (pushforward f ⋙ restrictFunctor g))
#check (AlgebraicGeometry.AlgebraicSpace.Modules.derivedPushforwardRestrictComposite_isRightDerived :
  ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    [Etale g] [Etale h],
    (modulesHomotopyFunctor (pushforward f ⋙ restrictFunctor g)).IsRightDerivedFunctor
      (derivedPushforwardRestrictCompositeUnit)
      (@HomotopyCategory.quasiIso X.Modules _ ℤ (up ℤ) X.modulesAbelian.toPreadditive inferInstance))
#check (AlgebraicGeometry.AlgebraicSpace.Modules.derivedRestrictPushforwardCompositeUnit :
  ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    [Etale g] [Etale h],
    modulesMapHomotopy (restrictFunctor h) ⋙ modulesHomotopyToDerived (pushforward f') ⟶
      modulesQh X ⋙ modulesHomotopyFunctor (restrictFunctor h ⋙ pushforward f'))
#check (AlgebraicGeometry.AlgebraicSpace.Modules.derivedRestrictPushforwardComposite_isRightDerived :
  ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    [Etale g] [Etale h],
    (modulesHomotopyFunctor (restrictFunctor h ⋙ pushforward f')).IsRightDerivedFunctor
      (derivedRestrictPushforwardCompositeUnit)
      (@HomotopyCategory.quasiIso X.Modules _ ℤ (up ℤ) X.modulesAbelian.toPreadditive inferInstance))
#check (AlgebraicGeometry.AlgebraicSpace.Modules.derivedPushforwardRestrictComparison :
  ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    [Etale g] [Etale h],
    modulesHomotopyFunctor (pushforward f ⋙ restrictFunctor g) ⟶
      moduleDerivedPushforward f ⋙ restrictFunctorDerived g)
#check (AlgebraicGeometry.AlgebraicSpace.Modules.isIso_derivedPushforwardRestrictComparison :
  ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    [Etale g] [Etale h],
    IsIso (derivedPushforwardRestrictComparison :
      modulesHomotopyFunctor (pushforward f ⋙ restrictFunctor g) ⟶
        moduleDerivedPushforward f ⋙ restrictFunctorDerived g))
#check (AlgebraicGeometry.AlgebraicSpace.Modules.derivedRestrictPushforwardComparison :
  ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    [Etale g] [Etale h],
    modulesHomotopyFunctor (restrictFunctor h ⋙ pushforward f') ⟶
      restrictFunctorDerived h ⋙ moduleDerivedPushforward f')
#check (AlgebraicGeometry.AlgebraicSpace.Modules.isIso_derivedRestrictPushforwardComparison :
  ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    [Etale g] [Etale h],
    IsIso (derivedRestrictPushforwardComparison :
      modulesHomotopyFunctor (restrictFunctor h ⋙ pushforward f') ⟶
        restrictFunctorDerived h ⋙ moduleDerivedPushforward f'))
#check (AlgebraicGeometry.AlgebraicSpace.Modules.derivedPushforwardEtaleBaseChangeNatIso :
  ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    [Etale g] [Etale h] (h_cart : IsPullback h f' f g),
    moduleDerivedPushforward f ⋙ restrictFunctorDerived g ≅
      restrictFunctorDerived h ⋙ moduleDerivedPushforward f')
#check (AlgebraicGeometry.AlgebraicSpace.Modules.derivedPushforwardEtaleBaseChangeHom :
  ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    [Etale g] [Etale h] (h_cart : IsPullback h f' f g) (E : ModuleDerived X),
    (restrictFunctorDerived g).obj ((moduleDerivedPushforward f).obj E) ⟶
      (moduleDerivedPushforward f').obj ((restrictFunctorDerived h).obj E))
#check (AlgebraicGeometry.AlgebraicSpace.Modules.isIso_derivedPushforwardEtaleBaseChangeHom :
  ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    [Etale g] [Etale h] (h_cart : IsPullback h f' f g) (E : ModuleDerived X),
    IsIso (derivedPushforwardEtaleBaseChangeHom h_cart E))
#check (AlgebraicGeometry.AlgebraicSpace.Modules.derivedPushforwardEtaleBaseChangeIso :
  ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    [Etale g] [Etale h] (h_cart : IsPullback h f' f g) (E : ModuleDerived X),
    (restrictFunctorDerived g).obj ((moduleDerivedPushforward f).obj E) ≅
      (moduleDerivedPushforward f').obj ((restrictFunctorDerived h).obj E))
#check (AlgebraicGeometry.AlgebraicSpace.Modules.derivedPushforwardEtaleBaseChangeIso_hom :
  ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    [Etale g] [Etale h] (h_cart : IsPullback h f' f g) (E : ModuleDerived X),
    (derivedPushforwardEtaleBaseChangeIso h_cart E).hom =
      derivedPushforwardEtaleBaseChangeHom h_cart E)
#check (AlgebraicGeometry.AlgebraicSpace.Modules.derivedPushforwardEtaleBaseChangeIso_of_hasPullback :
  ∀ {S : Scheme.{u}} {X Y V : AlgebraicSpace S} (f : X ⟶ Y) (g : V ⟶ Y)
    [Etale g] [HasPullback f g] (E : ModuleDerived X),
    (restrictFunctorDerived g).obj ((moduleDerivedPushforward f).obj E) ≅
      (moduleDerivedPushforward (Limits.pullback.snd f g)).obj
        ((restrictFunctorDerived (Limits.pullback.fst f g)).obj E))
