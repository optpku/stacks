/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap66.Lemma_66_18_12_Comparison
public import stacks_project.Chap66.«66_26_1_1_Restrict»

/-!
# Étale base change for module pushforward on algebraic spaces

A cartesian square of algebraic spaces with étale bottom edge induces a canonical comparison
`(f_* F)|_{Y'} ⟶ f'_*(F|_{X'})` of sheaves of modules on the small étale sites. Invertibility
is the Beck--Chevalley property of Properties of Spaces, lemma-pushforward-etale-base-change-modules.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.Sheaf.InternalModule RingedSite.ToposHom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}

/-- Pullback commutes around the given cartesian square by the actual composition maps. -/
def etaleBaseChangePullbackIso {X' X Y' Y : AlgebraicSpace S}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (h_cart : IsPullback h f' f g) :
    pullback g ⋙ pullback f' ≅ pullback f ⋙ pullback h :=
  pullbackCompIso f' g ≪≫ eqToIso (congrArg pullback h_cart.w.symm) ≪≫
    (pullbackCompIso h f).symm

/-- The actual pullback unit, cartesian comparison and counit give the base-change map. -/
def etaleBaseChangeModuleMap {X' X Y' Y : AlgebraicSpace S}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (h_cart : IsPullback h f' f g) [Etale g] [Etale h] (F : X.Modules) :
    (restrictFunctor g).obj ((pushforward f).obj F) ⟶
      (pushforward f').obj ((restrictFunctor h).obj F) :=
  (restrictFunctorIsoPullback g).hom.app ((pushforward f).obj F) ≫
    ((pullbackPushforwardAdjunction f').homEquiv _ _)
      ((etaleBaseChangePullbackIso h_cart).hom.app ((pushforward f).obj F) ≫
        (pullback h).map ((pullbackPushforwardAdjunction f).counit.app F)) ≫
    (pushforward f').map ((restrictFunctorIsoPullback h).inv.app F)

/-- The underlying type-valued morphism of `(f_* F)|_{Y'} ⟶ f'_*(F|_{X'})`. -/
def pushforwardEtaleBaseChangeUnderlying {X' X Y' Y : AlgebraicSpace S}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (h_cart : IsPullback h f' f g) [Etale g] [Etale h] (F : X.Modules) :
    (ToInternal.underlying (structureSheaf Y')).obj
      ((restrictFunctor g).obj ((pushforward f).obj F)) ⟶
    (ToInternal.underlying (structureSheaf Y')).obj
      ((pushforward f').obj ((restrictFunctor h).obj F)) :=
  (ToInternal.underlying (structureSheaf Y')).map (etaleBaseChangeModuleMap h_cart F)

/-- The canonical base-change morphism `(f_* F)|_{Y'} ⟶ f'_*(F|_{X'})` of sheaves of modules on
`Y'_étale`. -/
def pushforwardEtaleBaseChangeHom {X' X Y' Y : AlgebraicSpace S}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (h_cart : IsPullback h f' f g) [Etale g] [Etale h] (F : X.Modules) :
    (restrictFunctor g).obj ((pushforward f).obj F) ⟶
      (pushforward f').obj ((restrictFunctor h).obj F) :=
  homOfUnderlying (structureSheaf Y') (pushforwardEtaleBaseChangeUnderlying h_cart F)
    sorry sorry

/-- The canonical base-change 2-cell `(f_* -)|_{Y'} ⟶ f'_*((-)|_{X'})` as a natural transformation
of module functors, for a cartesian square with étale vertical edges. -/
def pushforwardEtaleBaseChangeNatTrans {X' X Y' Y : AlgebraicSpace S}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (h_cart : IsPullback h f' f g) [Etale g] [Etale h] :
    pushforward f ⋙ restrictFunctor g ⟶ restrictFunctor h ⋙ pushforward f' where
  app F := pushforwardEtaleBaseChangeHom h_cart F
  naturality := sorry

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
