/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.EtaleBaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.LowerShriek

/-!
# Étale base change for lower shriek of modules

A cartesian square of algebraic spaces with étale edges induces a canonical identification
`(j_! F)|_V ≅ jW_!(F|_W)` for module sheaves. The underived comparison is the mate of the
forward pushforward Beck--Chevalley morphism of the flipped square along `j_! ⊣ j^*` and
`j^* ⊣ j_*`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits CategoryTheory.Functor

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
variable {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
variable [Etale f] [Etale f'] [Etale g] [Etale h]

/-- The underived étale lower-shriek comparison 2-cell, obtained as the mate of the forward
pushforward Beck--Chevalley morphism of the flipped cartesian square. -/
def lowerShriekEtaleBaseChangeNatTrans (h_cart : IsPullback h f' f g) :
    restrictFunctor h ⋙ lowerShriek f' ⟶ lowerShriek f ⋙ restrictFunctor g :=
  (conjugateEquiv
      ((lowerShriekAdjunction f).comp (restrictAdjunction g))
      ((restrictAdjunction h).comp (lowerShriekAdjunction f'))).symm
    (pushforwardEtaleBaseChangeNatTrans h_cart.flip)

/-- The mate of the forward pushforward comparison is an isomorphism. -/
instance isIso_lowerShriekEtaleBaseChangeNatTrans_app (h_cart : IsPullback h f' f g)
    (F : X.Modules) :
    IsIso ((lowerShriekEtaleBaseChangeNatTrans h_cart).app F) :=
  sorry

/-- The canonical underived base-change morphism `(j_! F)|_{Y'} ⟶ jW_!(F|_{X'})` of sheaves of
modules, obtained by orienting the mate of the forward pushforward comparison. -/
def lowerShriekEtaleBaseChangeHom (h_cart : IsPullback h f' f g) (F : X.Modules) :
    (restrictFunctor g).obj ((lowerShriek f).obj F) ⟶
      (lowerShriek f').obj ((restrictFunctor h).obj F) :=
  (asIso ((lowerShriekEtaleBaseChangeNatTrans h_cart).app F)).inv

/-- The identification `(j_! F)|_{Y'} ≅ jW_!(F|_{X'})` of sheaves of modules. -/
def lowerShriekEtaleBaseChangeIso (h_cart : IsPullback h f' f g) (F : X.Modules) :
    (restrictFunctor g).obj ((lowerShriek f).obj F) ≅
      (lowerShriek f').obj ((restrictFunctor h).obj F) :=
  (asIso ((lowerShriekEtaleBaseChangeNatTrans h_cart).app F)).symm

/-- The underived étale lower-shriek comparison morphism is an isomorphism. -/
instance isIso_lowerShriekEtaleBaseChangeHom (h_cart : IsPullback h f' f g)
    (F : X.Modules) :
    IsIso (lowerShriekEtaleBaseChangeHom h_cart F) :=
  Iso.isIso_hom (lowerShriekEtaleBaseChangeIso h_cart F)

/-- The underived étale lower-shriek Beck--Chevalley isomorphism of module functors. -/
def lowerShriekEtaleBaseChangeNatIso (h_cart : IsPullback h f' f g) :
    lowerShriek f ⋙ restrictFunctor g ≅ restrictFunctor h ⋙ lowerShriek f' :=
  NatIso.ofComponents (fun F ↦ lowerShriekEtaleBaseChangeIso h_cart F) sorry

/-- The forward map of the underived étale lower-shriek isomorphism is the comparison
morphism. -/
theorem lowerShriekEtaleBaseChangeIso_hom (h_cart : IsPullback h f' f g)
    (F : X.Modules) :
    (lowerShriekEtaleBaseChangeIso h_cart F).hom =
      lowerShriekEtaleBaseChangeHom h_cart F :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Modules
