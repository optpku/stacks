module

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

/-- Direct image of type-valued sheaves in universe `u` is the coefficient-specialization of
`sheafPushforward`. -/
def typePushforwardIsoSheafPushforward {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    typePushforward f ≅ sheafPushforward (Type u) f :=
  Iso.refl _

/-- The underlying type-valued morphism of `(f_* F)|_{Y'} ⟶ f'_*(F|_{X'})`. -/
def pushforwardEtaleBaseChangeUnderlying {X' X Y' Y : AlgebraicSpace S}
    {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (h_cart : IsPullback h f' f g) [Etale g] [Etale h] (F : X.Modules) :
    (ToInternal.underlying (structureSheaf Y')).obj
      ((restrictFunctor g).obj ((pushforward f).obj F)) ⟶
    (ToInternal.underlying (structureSheaf Y')).obj
      ((pushforward f').obj ((restrictFunctor h).obj F)) :=
  (restrictFunctorIsoInverseImage g).hom.app ((pushforward f).obj F) ≫
    (etaleRestrictionSheaf g (Type u)).map
      ((ModulePushforward.forgetIso (ringedToposHom f)).hom.app F ≫
        (typePushforwardIsoSheafPushforward f).hom.app
          ((ToInternal.underlying (structureSheaf X)).obj F)) ≫
    (AlgebraicGeometry.AlgebraicSpace.pushforwardEtaleBaseChangeHom h_cart (Type u)
      ((ToInternal.underlying (structureSheaf X)).obj F)) ≫
    (sheafPushforward (Type u) f').map ((restrictFunctorIsoInverseImage h).inv.app F) ≫
      (typePushforwardIsoSheafPushforward f').inv.app
          ((ToInternal.underlying (structureSheaf X')).obj ((restrictFunctor h).obj F)) ≫
        (ModulePushforward.forgetIso (ringedToposHom f')).inv.app ((restrictFunctor h).obj F)

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
