module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.Preadditive
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.Naturality
public import ReasLib.CategoryTheory.Functor.Derived.Composition.Right
public import ReasLib.CategoryTheory.Functor.Derived.Exact
public import stacks_project.Chap67.«67_11_1_1_Comparison»
public import stacks_project.Chap75.Lemma_75_11_2_Coherator
public import stacks_project.Chap75.Lemma_75_3_1_Pushforward
public import stacks_project.Chap75.Lemma_75_3_1_Restrict

/-!
# Étale base change for derived pushforward of modules

A cartesian square of algebraic spaces with étale vertical edges induces a canonical
identification `(Rf_* E)|_{Y'} ≅ Rf'_*(E|_{X'})` in `D(𝒪_{Y'})`. The comparison is an
isomorphism of composites of the chosen derived functors `pushforwardDerived` and
`restrictFunctorDerived`, assembled from the underived étale Beck--Chevalley isomorphism,
the exactness identification of étale restriction, and the right-derived composition
comparison `R(G ∘ F) ⟶ RG ∘ RF`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits CategoryTheory.Functor
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}

/-- Homotopy category of `𝒪`-modules, using the `modulesAbelian` preadditive structure. -/
abbrev modulesHomotopy (X : AlgebraicSpace S) :=
  @HomotopyCategory ℤ X.Modules _ X.modulesAbelian.toPreadditive (up ℤ)

/-- Localization `K(𝒪_X) ⥤ D(𝒪_X)` with the `modulesAbelian` preadditive structure. -/
abbrev modulesQh (X : AlgebraicSpace S) :
    modulesHomotopy X ⥤ ModuleDerived X :=
  @DerivedCategory.Qh X.Modules _ X.modulesAbelian (modulesHasDerivedCategory X)

/-- Induced functor of homotopy categories of `𝒪`-modules. -/
abbrev modulesMapHomotopy {X Y : AlgebraicSpace S} (F : X.Modules ⥤ Y.Modules)
    [F.Additive] :
    modulesHomotopy X ⥤ modulesHomotopy Y :=
  @mapHomotopyCategory ℤ X.Modules _ X.modulesAbelian.toPreadditive
    Y.Modules _ Y.modulesAbelian.toPreadditive F inferInstance (up ℤ)

/-- Homotopy-to-derived functor of an additive functor of module categories. -/
abbrev modulesHomotopyToDerived {X Y : AlgebraicSpace S} (F : X.Modules ⥤ Y.Modules)
    [F.Additive] :
    modulesHomotopy X ⥤ ModuleDerived Y :=
  @Homotopy.toDerived X.Modules _ X.modulesAbelian.toPreadditive
    Y.Modules _ Y.modulesAbelian (modulesHasDerivedCategory Y) F inferInstance

/-- K-injective total right-derived functor of an additive functor of module categories. -/
abbrev modulesHomotopyFunctor {X Y : AlgebraicSpace S} (F : X.Modules ⥤ Y.Modules)
    [F.Additive] :
    ModuleDerived X ⥤ ModuleDerived Y :=
  @RightDerived.KInjective.functor.{u} X.Modules _ X.modulesAbelian
    Y.Modules _ Y.modulesAbelian (modulesHasDerivedCategory X)
    (modulesHasDerivedCategory Y) F inferInstance
    (inferInstance : IsGrothendieckAbelian.{u} X.Modules) inferInstance

/-- Homotopy-level unit of a K-injective total right-derived functor of modules. -/
abbrev modulesHomotopyUnit {X Y : AlgebraicSpace S} (F : X.Modules ⥤ Y.Modules)
    [F.Additive] :
    modulesHomotopyToDerived F ⟶ modulesQh X ⋙ modulesHomotopyFunctor F :=
  @RightDerived.Homotopy.unit X.Modules _ X.modulesAbelian (modulesHasDerivedCategory X)
    Y.Modules _ Y.modulesAbelian (modulesHasDerivedCategory Y) F inferInstance inferInstance

/-- Homotopy-level exactness unit of étale restriction. -/
abbrev modulesRestrictFactorshInv {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f]
    [(restrictFunctor f).Additive]
    [PreservesFiniteLimits (restrictFunctor f)]
    [PreservesFiniteColimits (restrictFunctor f)] :
    modulesHomotopyToDerived (restrictFunctor f) ⟶
      modulesQh Y ⋙ restrictFunctorDerived f :=
  (@mapDerivedCategoryFactorsh Y.Modules _ Y.modulesAbelian (modulesHasDerivedCategory Y)
    X.Modules _ X.modulesAbelian (modulesHasDerivedCategory X)
    (restrictFunctor f) inferInstance inferInstance inferInstance).inv

variable {X' X Y' Y : AlgebraicSpace S}
variable {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
variable [Etale g] [Etale h]
variable [(pushforward f).Additive] [(pushforward f').Additive]
variable [(restrictFunctor g).Additive] [(restrictFunctor h).Additive]
variable [PreservesFiniteLimits (restrictFunctor g)]
variable [PreservesFiniteColimits (restrictFunctor g)]
variable [PreservesFiniteLimits (restrictFunctor h)]
variable [PreservesFiniteColimits (restrictFunctor h)]

/-- The underived étale Beck--Chevalley isomorphism of module functors. -/
def pushforwardEtaleBaseChangeNatIso (h_cart : IsPullback h f' f g) :
    pushforward f ⋙ restrictFunctor g ≅ restrictFunctor h ⋙ pushforward f' :=
  NatIso.ofComponents (fun F ↦ pushforwardEtaleBaseChangeIso h_cart F) sorry

/-- Homotopy-to-derived unit of the underived left composite `(f_* -)|_{Y'}`. -/
def derivedPushforwardRestrictCompositeUnit :
    modulesMapHomotopy (pushforward f) ⋙ modulesHomotopyToDerived (restrictFunctor g) ⟶
      modulesQh X ⋙ modulesHomotopyFunctor (pushforward f ⋙ restrictFunctor g) :=
  (associator
      (modulesMapHomotopy (pushforward f))
      (modulesMapHomotopy (restrictFunctor g))
      (modulesQh Y')).hom ≫
    (isoWhiskerRight
        (mapHomotopyCategoryCompIso (Iso.refl (pushforward f ⋙ restrictFunctor g)) (up ℤ))
        (modulesQh Y')).hom ≫
      modulesHomotopyUnit (pushforward f ⋙ restrictFunctor g)

/-- The K-injective derived functor of the underived left composite is a right-derived
model of that composite. -/
instance derivedPushforwardRestrictComposite_isRightDerived :
    (modulesHomotopyFunctor (pushforward f ⋙ restrictFunctor g)).IsRightDerivedFunctor
      derivedPushforwardRestrictCompositeUnit
      (@HomotopyCategory.quasiIso X.Modules _ ℤ (up ℤ) X.modulesAbelian.toPreadditive
        inferInstance) :=
  sorry

/-- Homotopy-to-derived unit of the underived right composite `f'_*((-)|_{X'})`. -/
def derivedRestrictPushforwardCompositeUnit :
    modulesMapHomotopy (restrictFunctor h) ⋙ modulesHomotopyToDerived (pushforward f') ⟶
      modulesQh X ⋙ modulesHomotopyFunctor (restrictFunctor h ⋙ pushforward f') :=
  (associator
      (modulesMapHomotopy (restrictFunctor h))
      (modulesMapHomotopy (pushforward f'))
      (modulesQh Y')).hom ≫
    (isoWhiskerRight
        (mapHomotopyCategoryCompIso (Iso.refl (restrictFunctor h ⋙ pushforward f')) (up ℤ))
        (modulesQh Y')).hom ≫
      modulesHomotopyUnit (restrictFunctor h ⋙ pushforward f')

/-- The K-injective derived functor of the underived right composite is a right-derived
model of that composite. -/
instance derivedRestrictPushforwardComposite_isRightDerived :
    (modulesHomotopyFunctor (restrictFunctor h ⋙ pushforward f')).IsRightDerivedFunctor
      derivedRestrictPushforwardCompositeUnit
      (@HomotopyCategory.quasiIso X.Modules _ ℤ (up ℤ) X.modulesAbelian.toPreadditive
        inferInstance) :=
  sorry

/-- Right-derived composition comparison
`R((f_* -)|_{Y'}) ⟶ Rf_* ⋙ (-)|_{Y'}`. -/
def derivedPushforwardRestrictComparison :
    modulesHomotopyFunctor (pushforward f ⋙ restrictFunctor g) ⟶
      pushforwardDerived f ⋙ restrictFunctorDerived g :=
  @RightDerived.Composition.comparisonOfModels
    (modulesHomotopy X) (modulesHomotopy Y) (ModuleDerived Y')
    (ModuleDerived X) (ModuleDerived Y)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (modulesMapHomotopy (pushforward f))
    (modulesHomotopyToDerived (restrictFunctor g))
    (modulesQh X) (modulesQh Y)
    (pushforwardDerived f) (restrictFunctorDerived g)
    (modulesHomotopyFunctor (pushforward f ⋙ restrictFunctor g))
    (@HomotopyCategory.quasiIso X.Modules _ ℤ (up ℤ) X.modulesAbelian.toPreadditive
      inferInstance)
    (modulesHomotopyUnit (pushforward f))
    (modulesRestrictFactorshInv g)
    derivedPushforwardRestrictCompositeUnit
    inferInstance inferInstance

/-- The left composition comparison is an isomorphism. -/
instance isIso_derivedPushforwardRestrictComparison :
    IsIso (derivedPushforwardRestrictComparison :
      modulesHomotopyFunctor (pushforward f ⋙ restrictFunctor g) ⟶
        pushforwardDerived f ⋙ restrictFunctorDerived g) :=
  sorry

/-- Right-derived composition comparison
`R(f'_*((-)|_{X'})) ⟶ (-)|_{X'} ⋙ Rf'_*`. -/
def derivedRestrictPushforwardComparison :
    modulesHomotopyFunctor (restrictFunctor h ⋙ pushforward f') ⟶
      restrictFunctorDerived h ⋙ pushforwardDerived f' :=
  @RightDerived.Composition.comparisonOfModels
    (modulesHomotopy X) (modulesHomotopy X') (ModuleDerived Y')
    (ModuleDerived X) (ModuleDerived X')
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (modulesMapHomotopy (restrictFunctor h))
    (modulesHomotopyToDerived (pushforward f'))
    (modulesQh X) (modulesQh X')
    (restrictFunctorDerived h) (pushforwardDerived f')
    (modulesHomotopyFunctor (restrictFunctor h ⋙ pushforward f'))
    (@HomotopyCategory.quasiIso X.Modules _ ℤ (up ℤ) X.modulesAbelian.toPreadditive
      inferInstance)
    (modulesRestrictFactorshInv h)
    (modulesHomotopyUnit (pushforward f'))
    derivedRestrictPushforwardCompositeUnit
    inferInstance inferInstance

/-- The right composition comparison is an isomorphism. -/
instance isIso_derivedRestrictPushforwardComparison :
    IsIso (derivedRestrictPushforwardComparison :
      modulesHomotopyFunctor (restrictFunctor h ⋙ pushforward f') ⟶
        restrictFunctorDerived h ⋙ pushforwardDerived f') :=
  sorry

/-- Transport of the underived étale Beck--Chevalley isomorphism to K-injective total
right-derived functors of the underived composites. -/
def derivedPushforwardEtaleBaseChangeMiddleIso (h_cart : IsPullback h f' f g) :
    modulesHomotopyFunctor (pushforward f ⋙ restrictFunctor g) ≅
      modulesHomotopyFunctor (restrictFunctor h ⋙ pushforward f') :=
  @RightDerived.Homotopy.mapNatIso X.Modules _ X.modulesAbelian (modulesHasDerivedCategory X)
    Y'.Modules _ Y'.modulesAbelian (modulesHasDerivedCategory Y')
    (pushforward f ⋙ restrictFunctor g) (restrictFunctor h ⋙ pushforward f')
    inferInstance inferInstance inferInstance inferInstance
    (pushforwardEtaleBaseChangeNatIso h_cart)

/-- The derived étale Beck--Chevalley isomorphism of functors on `D(𝒪_X)`. -/
def derivedPushforwardEtaleBaseChangeNatIso (h_cart : IsPullback h f' f g) :
    pushforwardDerived f ⋙ restrictFunctorDerived g ≅
      restrictFunctorDerived h ⋙ pushforwardDerived f' :=
  (asIso derivedPushforwardRestrictComparison).symm ≪≫
    derivedPushforwardEtaleBaseChangeMiddleIso h_cart ≪≫
      asIso derivedRestrictPushforwardComparison

/-- The canonical derived base-change morphism
`(Rf_* E)|_{Y'} ⟶ Rf'_*(E|_{X'})` in `D(𝒪_{Y'})`. -/
def derivedPushforwardEtaleBaseChangeHom (h_cart : IsPullback h f' f g)
    (E : ModuleDerived X) :
    (restrictFunctorDerived g).obj ((pushforwardDerived f).obj E) ⟶
      (pushforwardDerived f').obj ((restrictFunctorDerived h).obj E) :=
  (derivedPushforwardEtaleBaseChangeNatIso h_cart).hom.app E

/-- The derived étale base-change morphism is an isomorphism. -/
instance isIso_derivedPushforwardEtaleBaseChangeHom (h_cart : IsPullback h f' f g)
    (E : ModuleDerived X) :
    IsIso (derivedPushforwardEtaleBaseChangeHom h_cart E) :=
  sorry

/-- The identification `(Rf_* E)|_{Y'} ≅ Rf'_*(E|_{X'})` in `D(𝒪_{Y'})`. -/
def derivedPushforwardEtaleBaseChangeIso (h_cart : IsPullback h f' f g)
    (E : ModuleDerived X) :
    (restrictFunctorDerived g).obj ((pushforwardDerived f).obj E) ≅
      (pushforwardDerived f').obj ((restrictFunctorDerived h).obj E) :=
  (derivedPushforwardEtaleBaseChangeNatIso h_cart).app E

/-- The forward map of the derived étale base-change isomorphism is the comparison morphism. -/
theorem derivedPushforwardEtaleBaseChangeIso_hom (h_cart : IsPullback h f' f g)
    (E : ModuleDerived X) :
    (derivedPushforwardEtaleBaseChangeIso h_cart E).hom =
      derivedPushforwardEtaleBaseChangeHom h_cart E :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Modules

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y V : AlgebraicSpace S}

/-- Source-facing specialization: restriction of `Rf_* E` along étale `g : V ⟶ Y` is
identified with the derived pushforward of the restriction of `E` to `U = V ×_Y X`,
modelled as the mathlib pullback `X ×_Y V`. -/
def derivedPushforwardEtaleBaseChangeIso_of_hasPullback
    (f : X ⟶ Y) (g : V ⟶ Y)
    [Etale g] [HasPullback f g] [Etale (Limits.pullback.fst f g)]
    [(pushforward f).Additive]
    [(pushforward (Limits.pullback.snd f g)).Additive]
    [(restrictFunctor g).Additive]
    [(restrictFunctor (Limits.pullback.fst f g)).Additive]
    [PreservesFiniteLimits (restrictFunctor g)]
    [PreservesFiniteColimits (restrictFunctor g)]
    [PreservesFiniteLimits (restrictFunctor (Limits.pullback.fst f g))]
    [PreservesFiniteColimits (restrictFunctor (Limits.pullback.fst f g))]
    (E : ModuleDerived X) :
    (restrictFunctorDerived g).obj ((pushforwardDerived f).obj E) ≅
      (pushforwardDerived (Limits.pullback.snd f g)).obj
        ((restrictFunctorDerived (Limits.pullback.fst f g)).obj E) :=
  derivedPushforwardEtaleBaseChangeIso (IsPullback.of_hasPullback f g) E

end AlgebraicGeometry.AlgebraicSpace.Modules
