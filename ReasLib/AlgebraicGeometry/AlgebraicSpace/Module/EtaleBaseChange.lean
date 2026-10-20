/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.PresentationRestriction

/-! # Étale base change for module pushforward on algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}

/-- The canonical restriction comparison for a cartesian square with étale vertical edges. -/
def pushforwardEtaleBaseChangeNatTrans {X' X Y' Y : AlgebraicSpace S}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (h_cart : IsPullback h f' f g) [Etale g] [Etale h] :
    pushforward f ⋙ restrictFunctor g ⟶ restrictFunctor h ⋙ pushforward f' :=
  Functor.whiskerLeft (pushforward f) (restrictFunctorIsoPullback g).hom ≫
    baseChange h_cart.w ≫
    Functor.whiskerRight (restrictFunctorIsoPullback h).inv (pushforward f')

/-- The canonical comparison from restriction of a pushforward to pushforward of restriction. -/
def pushforwardEtaleBaseChangeHom {X' X Y' Y : AlgebraicSpace S}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (h_cart : IsPullback h f' f g) [Etale g] [Etale h] (F : X.Modules) :
    (restrictFunctor g).obj ((pushforward f).obj F) ⟶
      (pushforward f').obj ((restrictFunctor h).obj F) :=
  (pushforwardEtaleBaseChangeNatTrans h_cart).app F

/-- The module comparison morphism is the component of the base-change natural transformation. -/
theorem pushforwardEtaleBaseChangeHom_eq {X' X Y' Y : AlgebraicSpace S}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (h_cart : IsPullback h f' f g) [Etale g] [Etale h] (F : X.Modules) :
    pushforwardEtaleBaseChangeHom h_cart F =
      (pushforwardEtaleBaseChangeNatTrans h_cart).app F :=
  rfl

/-- The module comparison morphism is an isomorphism, for a cartesian square with étale bottom
edge. -/
instance isIso_pushforwardEtaleBaseChangeHom {X' X Y' Y : AlgebraicSpace S}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (h_cart : IsPullback h f' f g) [Etale g] [Etale h] (F : X.Modules) :
    IsIso (pushforwardEtaleBaseChangeHom h_cart F) :=
  sorry

/-- The identification `(f_* F)|_{Y'} ≅ f'_*(F|_{X'})` of sheaves of modules on `Y'_étale`. -/
def pushforwardEtaleBaseChangeIso {X' X Y' Y : AlgebraicSpace S}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (h_cart : IsPullback h f' f g) [Etale g] [Etale h] (F : X.Modules) :
    (restrictFunctor g).obj ((pushforward f).obj F) ≅
      (pushforward f').obj ((restrictFunctor h).obj F) :=
  asIso (pushforwardEtaleBaseChangeHom h_cart F)

/-- The forward map of the module base-change isomorphism is the comparison morphism. -/
theorem pushforwardEtaleBaseChangeIso_hom {X' X Y' Y : AlgebraicSpace S}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (h_cart : IsPullback h f' f g) [Etale g] [Etale h] (F : X.Modules) :
    (pushforwardEtaleBaseChangeIso h_cart F).hom =
      pushforwardEtaleBaseChangeHom h_cart F :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Modules
