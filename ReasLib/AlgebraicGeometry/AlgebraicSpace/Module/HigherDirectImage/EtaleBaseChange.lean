module

public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.PresentationRestriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.EtaleBaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HigherDirectImage

/-!
# Étale base change for higher direct images of modules

A cartesian square of algebraic spaces with étale vertical edges induces a canonical
identification `(R^i f_* F)|_{Y'} ≅ R^i f'_*(F|_{X'})` of sheaves of modules on `Y'_étale`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits CategoryTheory.Functor

noncomputable section

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Functor.RightDerived` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImageEtaleBaseChangeHom`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}

/-- Restriction of modules along an étale morphism of algebraic spaces is additive. -/
instance restrictFunctor_additive {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f]
    [Abelian X.Modules] [Abelian Y.Modules] :
    (restrictFunctor f).Additive :=
  sorry

/-- Restriction of modules along an étale morphism of algebraic spaces preserves homology. -/
instance restrictFunctor_preservesHomology {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f]
    [Abelian X.Modules] [Abelian Y.Modules] :
    (restrictFunctor f).PreservesHomology :=
  sorry

/-- Restriction of modules along an étale morphism of algebraic spaces preserves injective
objects. -/
instance restrictFunctor_preservesInjectiveObjects {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Etale f] [Abelian X.Modules] [Abelian Y.Modules] :
    (restrictFunctor f).PreservesInjectiveObjects :=
  sorry

variable {X' X Y' Y : AlgebraicSpace S}
variable {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The canonical base-change 2-cell
`(R^i f_* -)|_{Y'} ⟶ R^i f'_*((-)|_{X'})` as a natural transformation of module functors. -/
def higherDirectImageEtaleBaseChangeNatTrans (h_cart : IsPullback h f' f g)
    [Etale g] [Etale h]
    [Abelian X.Modules] [Abelian X'.Modules] [Abelian Y.Modules] [Abelian Y'.Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions X'.Modules] (i : ℕ) :
    higherDirectImageFunctor f i ⋙ restrictFunctor g ⟶
      restrictFunctor h ⋙ higherDirectImageFunctor f' i :=
  (RightDerived.postcompIso (pushforward f) (restrictFunctor g) i).inv ≫
    NatTrans.rightDerived (pushforwardEtaleBaseChangeNatTrans h_cart) i ≫
      (RightDerived.precompIso (restrictFunctor h) (pushforward f') i).hom

/-- The canonical higher-direct-image base-change morphism
`(R^i f_* F)|_{Y'} ⟶ R^i f'_*(F|_{X'})` of sheaves of modules on `Y'_étale`. -/
def higherDirectImageEtaleBaseChangeHom (h_cart : IsPullback h f' f g)
    [Etale g] [Etale h]
    [Abelian X.Modules] [Abelian X'.Modules] [Abelian Y.Modules] [Abelian Y'.Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions X'.Modules]
    (F : X.Modules) (i : ℕ) :
    (restrictFunctor g).obj (higherDirectImage f F i) ⟶
      higherDirectImage f' (restrict F h) i :=
  (higherDirectImageEtaleBaseChangeNatTrans h_cart i).app F

/-- The module higher-direct-image comparison morphism is the component of the derived
base-change natural transformation. -/
theorem higherDirectImageEtaleBaseChangeHom_eq (h_cart : IsPullback h f' f g)
    [Etale g] [Etale h]
    [Abelian X.Modules] [Abelian X'.Modules] [Abelian Y.Modules] [Abelian Y'.Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions X'.Modules]
    (F : X.Modules) (i : ℕ) :
    higherDirectImageEtaleBaseChangeHom h_cart F i =
      (higherDirectImageEtaleBaseChangeNatTrans h_cart i).app F :=
  rfl

/-- The identification `(R^i f_* F)|_{Y'} ≅ R^i f'_*(F|_{X'})` of sheaves of modules on
`Y'_étale`. -/
def higherDirectImageEtaleBaseChangeIso (h_cart : IsPullback h f' f g)
    [Etale g] [Etale h]
    [Abelian X.Modules] [Abelian X'.Modules] [Abelian Y.Modules] [Abelian Y'.Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions X'.Modules]
    (F : X.Modules) (i : ℕ) :
    (restrictFunctor g).obj (higherDirectImage f F i) ≅
      higherDirectImage f' (restrict F h) i :=
  ((RightDerived.postcompIso (pushforward f) (restrictFunctor g) i).symm ≪≫
    NatIso.rightDerived
      (NatIso.ofComponents (pushforwardEtaleBaseChangeIso h_cart)
        (fun φ ↦ (pushforwardEtaleBaseChangeNatTrans h_cart).naturality φ)) i ≪≫
    RightDerived.precompIso (restrictFunctor h) (pushforward f') i).app F

/-- The forward map of the module higher-direct-image base-change isomorphism is the comparison
morphism. -/
theorem higherDirectImageEtaleBaseChangeIso_hom (h_cart : IsPullback h f' f g)
    [Etale g] [Etale h]
    [Abelian X.Modules] [Abelian X'.Modules] [Abelian Y.Modules] [Abelian Y'.Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions X'.Modules]
    (F : X.Modules) (i : ℕ) :
    (higherDirectImageEtaleBaseChangeIso h_cart F i).hom =
      higherDirectImageEtaleBaseChangeHom h_cart F i :=
  rfl

/-- The module higher-direct-image comparison morphism is an isomorphism, for a cartesian
square with étale vertical edges. -/
instance isIso_higherDirectImageEtaleBaseChangeHom (h_cart : IsPullback h f' f g)
    [Etale g] [Etale h]
    [Abelian X.Modules] [Abelian X'.Modules] [Abelian Y.Modules] [Abelian Y'.Modules]
    [HasInjectiveResolutions X.Modules] [HasInjectiveResolutions X'.Modules]
    (F : X.Modules) (i : ℕ) :
    IsIso (higherDirectImageEtaleBaseChangeHom h_cart F i) :=
  by
    rw [← higherDirectImageEtaleBaseChangeIso_hom h_cart F i]
    infer_instance

end AlgebraicGeometry.AlgebraicSpace.Modules
