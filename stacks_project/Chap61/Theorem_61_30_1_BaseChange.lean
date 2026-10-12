/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.GroupTheory.Torsion
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Completion
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.ModuleAdjunction
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory
public import ReasLib.CategoryTheory.DerivedCategory.Bounded
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived.Composition
public import ReasLib.CategoryTheory.Functor.Derived.Adjunction.Restriction
public import ReasLib.CategoryTheory.Functor.Derived.Naturality.Left
public import ReasLib.CategoryTheory.Sites.GlobalSections.ToposMorphism
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import stacks_project.Chap61.Definition_61_28_1_Pullback
public import stacks_project.Chap61.Definition_61_29_1_Derived
import Mathlib.Tactic.CrossRefAttribute

/-!
# Completed derived base change on small pro-étale sites

Constant-coefficient morphisms of ringed topoi attached to scheme morphisms, the
restricted derived-complete pushforward and completed pullback, and the canonical
comparison `Lg_comp^* Rf_* K ⟶ Rf'_* L(g')_comp^* K`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open CategoryTheory.MorphismOfTopoiIn
open CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProetaleDerived
open RingedSite
open RingedSite.Hom
open RingedSite.Hom.ModuleDerived
open RingedSite.ToposHom
open SheafOfModules.RingedSite
open CategoryTheory.Sheaf.InternalModule

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.ProEt

/-- Forgetting the ring structure on `underline(Λ)` recovers the constant type-valued sheaf
on the small pro-étale site. -/
def constantCoefficientUnderlyingIso (Z : Scheme.{u}) (Λ : Type v) [CommRing Λ]
    [HasWeakSheafify (topology Z) CommRingCat.{v}]
    [HasWeakSheafify (topology Z) RingCat.{v}]
    [HasWeakSheafify (topology Z) (Type v)]
    [(topology Z).HasSheafCompose (forget₂ CommRingCat.{v} RingCat.{v})]
    [(topology Z).HasSheafCompose (CategoryTheory.forget RingCat.{v})]
    [(topology Z).PreservesSheafification (forget₂ CommRingCat.{v} RingCat.{v})]
    [(topology Z).PreservesSheafification (CategoryTheory.forget RingCat.{v})] :
    Hom.underlyingStructureSheaf
        (ofCommRingSheaf (topology Z) (constantCoefficientRing Z Λ)) ≅
      (constantSheaf (topology Z) (Type v)).obj Λ :=
  (sheafCompose (topology Z) (CategoryTheory.forget RingCat.{v})).mapIso
      ((constantCommuteCompose (topology Z)
          (forget₂ CommRingCat.{v} RingCat.{v})).app (CommRingCat.of Λ)) ≪≫
    (constantCommuteCompose (topology Z) (CategoryTheory.forget RingCat.{v})).app
      ((forget₂ CommRingCat.{v} RingCat.{v}).obj (CommRingCat.of Λ))

/-- The constant coefficient ideal sheaf of `I` on a specified scheme. -/
def coefficientIdeal (Z : Scheme.{u}) (Λ : Type v) [CommRing Λ] (I : Ideal Λ)
    [HasWeakSheafify (topology Z) CommRingCat.{v}]
    [HasWeakSheafify (topology Z) RingCat.{v}]
    [HasWeakSheafify (topology Z) AddCommGrpCat.{v}]
    [(topology Z).WEqualsLocallyBijective RingCat.{v}]
    [(topology Z).WEqualsLocallyBijective AddCommGrpCat.{v}]
    [(topology Z).HasSheafCompose (forget₂ CommRingCat.{v} RingCat.{v})]
    [(topology Z).HasSheafCompose (forget₂ RingCat.{v} AddCommGrpCat.{v})]
    [(topology Z).PreservesSheafification (forget₂ CommRingCat.{v} RingCat.{v})]
    [UnivLE.{u + 1, v}]
    [LocallySmall
        (SheafOfModules (ringSheafOfComm (constantCoefficientRing Z Λ)))]
    [WellPowered
        (SheafOfModules (ringSheafOfComm (constantCoefficientRing Z Λ)))] :
    Subobject (unitModule (topology Z) (constantCoefficientRing Z Λ)) :=
  (constantCoefficientIdeal :
      Ideal Λ → Subobject (unitModule (topology Z) (constantCoefficientRing Z Λ))) I

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (Λ : Type v) [CommRing Λ]
variable [HasWeakSheafify (topology X) CommRingCat.{v}]
variable [HasWeakSheafify (topology Y) CommRingCat.{v}]
variable [HasWeakSheafify (topology X) RingCat.{v}]
variable [HasWeakSheafify (topology Y) RingCat.{v}]
variable [HasWeakSheafify (topology X) (Type v)]
variable [HasWeakSheafify (topology Y) (Type v)]
variable [(topology X).HasSheafCompose (forget₂ CommRingCat.{v} RingCat.{v})]
variable [(topology Y).HasSheafCompose (forget₂ CommRingCat.{v} RingCat.{v})]
variable [(topology X).HasSheafCompose (CategoryTheory.forget RingCat.{v})]
variable [(topology Y).HasSheafCompose (CategoryTheory.forget RingCat.{v})]
variable [(topology X).PreservesSheafification (forget₂ CommRingCat.{v} RingCat.{v})]
variable [(topology Y).PreservesSheafification (forget₂ CommRingCat.{v} RingCat.{v})]
variable [(topology X).PreservesSheafification (CategoryTheory.forget RingCat.{v})]
variable [(topology Y).PreservesSheafification (CategoryTheory.forget RingCat.{v})]
variable [HasGlobalSectionsFunctor (topology X) (Type v)]
variable [HasGlobalSectionsFunctor (topology Y) (Type v)]
variable [∀ P : Y.ProEtᵒᵖ ⥤ Type v, (baseChange f).op.HasLeftKanExtension P]
variable [PreservesFiniteLimits
    ((baseChange f).sheafPullback (Type v) (topology Y) (topology X))]

/-- The morphism of topoi `Sh(X_proétale) ⟶ Sh(Y_proétale)` presented by pro-étale
base change along `f`. -/
def toMorphismOfTopoi : MorphismOfTopoiIn (topology Y) (topology X) :=
  (baseChange f).morphismOfTopoiInOfContinuous (topology Y) (topology X)

/-- Inverse image of the underlying type-valued sheaf of `underline(Λ)` along pro-étale
base change. -/
def ofConstantCoefficient_underlyingMap :
    (toMorphismOfTopoi f).inverseImage.obj
        (Hom.underlyingStructureSheaf
          (ofCommRingSheaf (topology Y) (constantCoefficientRing Y Λ))) ⟶
      Hom.underlyingStructureSheaf
        (ofCommRingSheaf (topology X) (constantCoefficientRing X Λ)) :=
  ((toMorphismOfTopoi f).inverseImage.mapIso
      (constantCoefficientUnderlyingIso Y Λ)).hom ≫
    (constantSheafCompInverseImageIso (toMorphismOfTopoi f)).hom.app Λ ≫
      (constantCoefficientUnderlyingIso X Λ).inv

/-- The type-valued inverse-image comparison for `underline(Λ)` after forgetting the
canonical ring inverse image. -/
def ofConstantCoefficient_ringUnderlyingMap :
    (sheafCompose (topology X) (CategoryTheory.forget RingCat.{v})).obj
        ((toMorphismOfTopoi f).ringInverseImage.obj
          (ofCommRingSheaf (topology Y) (constantCoefficientRing Y Λ)).structureSheaf) ⟶
      Hom.underlyingStructureSheaf
        (ofCommRingSheaf (topology X) (constantCoefficientRing X Λ)) :=
  (toMorphismOfTopoi f).ringInverseImageForgetIso.hom.app
      (ofCommRingSheaf (topology Y) (constantCoefficientRing Y Λ)).structureSheaf ≫
    ofConstantCoefficient_underlyingMap f Λ

/-- The inverse-image structure map `f⁻¹ underline(Λ)_Y ⟶ underline(Λ)_X` as a morphism
of ring-valued sheaves. Ring laws are deferred. -/
def ofConstantCoefficient_structureMap :
    (toMorphismOfTopoi f).ringInverseImage.obj
        (ofCommRingSheaf (topology Y) (constantCoefficientRing Y Λ)).structureSheaf ⟶
      (ofCommRingSheaf (topology X) (constantCoefficientRing X Λ)).structureSheaf where
  hom :=
    { app := fun U ↦
        let source : RingCat.{v} :=
          ((toMorphismOfTopoi f).ringInverseImage.obj
              (ofCommRingSheaf (topology Y)
                (constantCoefficientRing Y Λ)).structureSheaf).obj.obj U
        let target : RingCat.{v} :=
          (ofCommRingSheaf (topology X)
            (constantCoefficientRing X Λ)).structureSheaf.obj.obj U
        @RingCat.ofHom source target source.ring target.ring
        { toFun := (ofConstantCoefficient_ringUnderlyingMap f Λ).hom.app U
          map_one' := sorry
          map_mul' := sorry
          map_zero' := sorry
          map_add' := sorry }
      naturality := sorry }

/-- The morphism of ringed topoi `(X_proétale, underline(Λ)) ⟶ (Y_proétale, underline(Λ))`
attached to a scheme morphism `f : X ⟶ Y`. -/
def ofConstantCoefficient :
    ToposHom
      (ofCommRingSheaf (topology X) (constantCoefficientRing X Λ))
      (ofCommRingSheaf (topology Y) (constantCoefficientRing Y Λ)) where
  toTopos := toMorphismOfTopoi f
  structureMap := ofConstantCoefficient_structureMap f Λ

/-- The underlying morphism of topoi of `ofConstantCoefficient` is pro-étale base change. -/
theorem ofConstantCoefficient_toTopos :
    (ofConstantCoefficient f Λ).toTopos = toMorphismOfTopoi f := sorry

/-- Forgetting rings, the structure map of `ofConstantCoefficient` is the type-valued
constant sheaf comparison. -/
theorem ofConstantCoefficient_structureMap_spec :
    (ofConstantCoefficient f Λ).underlyingMap =
      ofConstantCoefficient_underlyingMap f Λ := sorry

/-- The structure map of `ofConstantCoefficient` is an isomorphism. -/
theorem ofConstantCoefficient_structureMap_isIso :
    IsIso (ofConstantCoefficient f Λ).structureMap := sorry

variable [UnivLE.{u + 1, v}]
variable [HasWeakSheafify (topology X) AddCommGrpCat.{v}]
variable [HasWeakSheafify (topology Y) AddCommGrpCat.{v}]
variable [(topology X).WEqualsLocallyBijective RingCat.{v}]
variable [(topology Y).WEqualsLocallyBijective RingCat.{v}]
variable [(topology X).WEqualsLocallyBijective AddCommGrpCat.{v}]
variable [(topology Y).WEqualsLocallyBijective AddCommGrpCat.{v}]
variable [(topology X).HasSheafCompose (forget₂ RingCat.{v} AddCommGrpCat.{v})]
variable [(topology Y).HasSheafCompose (forget₂ RingCat.{v} AddCommGrpCat.{v})]
variable [LocallySmall
    (SheafOfModules (ringSheafOfComm (constantCoefficientRing X Λ)))]
variable [LocallySmall
    (SheafOfModules (ringSheafOfComm (constantCoefficientRing Y Λ)))]
variable [WellPowered
    (SheafOfModules (ringSheafOfComm (constantCoefficientRing X Λ)))]
variable [WellPowered
    (SheafOfModules (ringSheafOfComm (constantCoefficientRing Y Λ)))]

/-- The constant coefficient ideal of `I` on `Y` (respectively `X`) is compatible with inverse
image along `ofConstantCoefficient`. -/
theorem mapsConstantCoefficientIdeal (I : Ideal Λ) :
    mapsIdeal (ofConstantCoefficient f Λ)
      (coefficientIdeal Y Λ I) (coefficientIdeal X Λ I) := sorry

variable [∀ U : X.ProEt, HasWeakSheafify ((topology X).over U) AddCommGrpCat.{v}]
variable [∀ U : X.ProEt, ((topology X).over U).WEqualsLocallyBijective AddCommGrpCat.{v}]
variable [∀ U : Y.ProEt, HasWeakSheafify ((topology Y).over U) AddCommGrpCat.{v}]
variable [∀ U : Y.ProEt, ((topology Y).over U).WEqualsLocallyBijective AddCommGrpCat.{v}]
variable [(SheafOfModules.restrictScalars
    (ofConstantCoefficient f Λ).structureMap).IsRightAdjoint]
variable [(ofConstantCoefficient f Λ).modulePullback.Additive]
variable [(ofConstantCoefficient f Λ).HasModulePullbackDerived]
variable [(ofConstantCoefficient f Λ).HasModulePushforwardDerived]
variable [(Functor.Homotopy.toDerived
    (ofConstantCoefficient f Λ).modulePullback).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules
        (ofCommRingSheaf (topology Y) (constantCoefficientRing Y Λ)).structureSheaf)
      (up ℤ))]

/-- Restricted derived pushforward `Rf_*` on `I`-complete objects of
`D(X_proétale, Λ)`. -/
abbrev completedPushforward (I : Ideal Λ) :
    (derivedCompleteObjectProperty
        (coefficientIdeal X Λ I)).FullSubcategory ⥤
      (derivedCompleteObjectProperty
        (coefficientIdeal Y Λ I)).FullSubcategory :=
  DerivedComplete.pushforward (ofConstantCoefficient f Λ)
    (coefficientIdeal Y Λ I) (coefficientIdeal X Λ I)
    (mapsConstantCoefficientIdeal f Λ I)

/-- Derived pullback on complete objects followed by derived completion,
`Lf_comp^*`, along `f`. -/
abbrev completedPullback (I : Ideal Λ)
    [(coefficientIdeal X Λ I :
        ringedSiteModuleCategory (topology X) (constantCoefficientRing X Λ)).IsFiniteType] :
    (derivedCompleteObjectProperty
        (coefficientIdeal Y Λ I)).FullSubcategory ⥤
      (derivedCompleteObjectProperty
        (coefficientIdeal X Λ I)).FullSubcategory :=
  DerivedComplete.pullback (ofConstantCoefficient f Λ)
    (coefficientIdeal Y Λ I)
    (Completion.reflector (coefficientIdeal X Λ I))

/-- Forgetting completeness, restricted pushforward is ambient derived pushforward. -/
abbrev completedPushforward_comp_inclusion (I : Ideal Λ) :
    completedPushforward f Λ I ⋙
        (derivedCompleteObjectProperty
          (coefficientIdeal Y Λ I)).ι ≅
      (derivedCompleteObjectProperty
          (coefficientIdeal X Λ I)).ι ⋙
        modulePushforwardDerived (ofConstantCoefficient f Λ) :=
  DerivedComplete.pushforwardCompInclusionIso (ofConstantCoefficient f Λ)
    (coefficientIdeal Y Λ I) (coefficientIdeal X Λ I)
    (mapsConstantCoefficientIdeal f Λ I)

/-- Forgetting completeness, `Lf_comp^*` is `Lf^*` followed by derived completion. -/
abbrev completedPullback_comp_inclusion (I : Ideal Λ)
    [(coefficientIdeal X Λ I :
        ringedSiteModuleCategory (topology X) (constantCoefficientRing X Λ)).IsFiniteType] :
    completedPullback f Λ I ⋙
        (derivedCompleteObjectProperty
          (coefficientIdeal X Λ I)).ι ≅
      (derivedCompleteObjectProperty
          (coefficientIdeal Y Λ I)).ι ⋙
        modulePullbackDerived (ofConstantCoefficient f Λ) ⋙
          (Completion.reflector (coefficientIdeal X Λ I)).reflection :=
  DerivedComplete.pullbackCompInclusionIso (ofConstantCoefficient f Λ)
    (coefficientIdeal Y Λ I)
    (Completion.reflector (coefficientIdeal X Λ I))

/-- Site-level base change along a cartesian square of schemes. -/
def baseChangeSquareIso {X' Y' : Scheme.{u}}
    (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X) (h_cart : IsPullback g' f' f g) :
    baseChange f ⋙ baseChange g' ≅ baseChange g ⋙ baseChange f' :=
  (baseChange_comp g' f).symm ≪≫
    eqToIso (congrArg baseChange h_cart.w) ≪≫
    baseChange_comp f' g

variable [HasWeakSheafify (topology X) (ModuleCat.{v} Λ)]
variable [Abelian (Sheaf (topology X) (ModuleCat.{v} Λ))]
variable [HasDerivedCategory (Sheaf (topology X) (ModuleCat.{v} Λ))]

/-- The constant-ringed complete object attached to a derived-complete object of
`D(X_proétale, Λ)`. -/
def toConstantComplete (I : Ideal Λ) (K : ProetaleDerived X Λ)
    (hK : IsDerivedCompleteWithRespectTo K I) :
    (derivedCompleteObjectProperty (coefficientIdeal X Λ I)).FullSubcategory :=
  ⟨toConstantModuleDerived K, hK⟩

/-- `toConstantComplete` packages derived completeness of the constant-ringed image. -/
theorem toConstantComplete_obj (I : Ideal Λ) (K : ProetaleDerived X Λ)
    (hK : IsDerivedCompleteWithRespectTo K I) :
    (toConstantComplete Λ I K hK).obj = toConstantModuleDerived K := sorry

/-- Lift an isomorphism of underlying type-valued sheaves to an isomorphism of
module sheaves. Additivity and scalar-linearity are deferred. -/
def moduleIsoOfUnderlying (W : Scheme.{u})
    [HasWeakSheafify (topology W) CommRingCat.{v}]
    [(topology W).HasSheafCompose (forget₂ CommRingCat.{v} RingCat.{v})]
    [(topology W).HasSheafCompose (CategoryTheory.forget RingCat.{v})]
    {M N :
      SheafOfModules.{v}
        (ofCommRingSheaf (topology W) (constantCoefficientRing W Λ)).structureSheaf}
    (e :
      (ToInternal.underlying
          (ofCommRingSheaf (topology W)
            (constantCoefficientRing W Λ)).structureSheaf).obj M ≅
        (ToInternal.underlying
          (ofCommRingSheaf (topology W)
            (constantCoefficientRing W Λ)).structureSheaf).obj N) :
    M ≅ N where
  hom := homOfUnderlying _ e.hom (fun _ _ _ ↦ sorry) (fun _ _ _ ↦ sorry)
  inv := homOfUnderlying _ e.inv (fun _ _ _ ↦ sorry) (fun _ _ _ ↦ sorry)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Module direct image along `ofConstantCoefficient` is additive. -/
instance ofConstantCoefficient_modulePushforward_additive :
    (ofConstantCoefficient f Λ).modulePushforward.Additive :=
  modulePushforward_additive _

variable [Adjunction.TotalDerived.HasPair
    (G := (ofConstantCoefficient f Λ).modulePullback.mapHomotopyCategory (up ℤ))
    (F := (ofConstantCoefficient f Λ).modulePushforward.mapHomotopyCategory (up ℤ))
    (ModuleQis (ofCommRingSheaf (topology Y) (constantCoefficientRing Y Λ)))
    (ModuleQis (ofCommRingSheaf (topology X) (constantCoefficientRing X Λ)))
    (L1 :=
      moduleLocalization
        (ofCommRingSheaf (topology Y) (constantCoefficientRing Y Λ)))
    (L2 :=
      moduleLocalization
        (ofCommRingSheaf (topology X) (constantCoefficientRing X Λ)))]

/-- The canonical derived pullback--pushforward adjunction along
`ofConstantCoefficient`. -/
def constantModuleDerivedAdjunction :
    modulePullbackDerived (ofConstantCoefficient f Λ) ⊣
      modulePushforwardDerived (ofConstantCoefficient f Λ) :=
  Adjunction.TotalDerived.HasPair.derived
    (Adjunction.mapHomotopyCategoryAdjunction
      (moduleAdjunction (ofConstantCoefficient f Λ)))
    (ModuleQis (ofCommRingSheaf (topology Y) (constantCoefficientRing Y Λ)))
    (ModuleQis (ofCommRingSheaf (topology X) (constantCoefficientRing X Λ)))

section CompAlong
variable {Z : Scheme.{u}} (h : Z ⟶ X)
variable [HasWeakSheafify (topology Z) CommRingCat.{v}]
variable [HasWeakSheafify (topology Z) RingCat.{v}]
variable [HasWeakSheafify (topology Z) (Type v)]
variable [(topology Z).HasSheafCompose (forget₂ CommRingCat.{v} RingCat.{v})]
variable [(topology Z).HasSheafCompose (CategoryTheory.forget RingCat.{v})]
variable [(topology Z).PreservesSheafification (forget₂ CommRingCat.{v} RingCat.{v})]
variable [(topology Z).PreservesSheafification (CategoryTheory.forget RingCat.{v})]
variable [HasGlobalSectionsFunctor (topology Z) (Type v)]
variable [∀ P : X.ProEtᵒᵖ ⥤ Type v, (baseChange h).op.HasLeftKanExtension P]
variable [PreservesFiniteLimits
    ((baseChange h).sheafPullback (Type v) (topology X) (topology Z))]
variable [∀ P : Y.ProEtᵒᵖ ⥤ Type v, (baseChange (h ≫ f)).op.HasLeftKanExtension P]
variable [PreservesFiniteLimits
    ((baseChange (h ≫ f)).sheafPullback (Type v) (topology Y) (topology Z))]
variable [(SheafOfModules.restrictScalars
    (ofConstantCoefficient h Λ).structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars
    (ToposHom.comp (ofConstantCoefficient h Λ)
      (ofConstantCoefficient f Λ)).structureMap).IsRightAdjoint]

/-- After forgetting to type-valued sheaves, module direct image along a composite is
the composite of the individual direct images. -/
def modulePushforwardCompUnderlyingIso :
    (ofConstantCoefficient h Λ).modulePushforward ⋙
      (ofConstantCoefficient f Λ).modulePushforward ⋙
        ToInternal.underlying
          (ofCommRingSheaf (topology Y)
            (constantCoefficientRing Y Λ)).structureSheaf ≅
      (ToposHom.comp (ofConstantCoefficient h Λ)
          (ofConstantCoefficient f Λ)).modulePushforward ⋙
        ToInternal.underlying
          (ofCommRingSheaf (topology Y)
            (constantCoefficientRing Y Λ)).structureSheaf :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (ofConstantCoefficient h Λ).modulePushforward
      (ModulePushforward.forgetIso (ofConstantCoefficient f Λ)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (ModulePushforward.forgetIso (ofConstantCoefficient h Λ))
      (ofConstantCoefficient f Λ).toTopos.pushforward ≪≫
    Functor.associator _ _ _ ≪≫
    (ModulePushforward.forgetIso
      (ToposHom.comp (ofConstantCoefficient h Λ)
        (ofConstantCoefficient f Λ))).symm

/-- Naturality of the type-valued composite direct-image comparison, after lifting to
module sheaves. -/
theorem modulePushforwardCompIso_naturality
    {M N :
      SheafOfModules.{v}
        (ofCommRingSheaf (topology Z) (constantCoefficientRing Z Λ)).structureSheaf}
    (φ : M ⟶ N) :
    ((ofConstantCoefficient h Λ).modulePushforward ⋙
            (ofConstantCoefficient f Λ).modulePushforward).map φ ≫
        (moduleIsoOfUnderlying Λ Y
          ((modulePushforwardCompUnderlyingIso f Λ h).app N)).hom =
      (moduleIsoOfUnderlying Λ Y
          ((modulePushforwardCompUnderlyingIso f Λ h).app M)).hom ≫
        (ToposHom.comp (ofConstantCoefficient h Λ)
            (ofConstantCoefficient f Λ)).modulePushforward.map φ := sorry

/-- Module direct image along a composite scheme morphism is the composite of the
individual direct images. -/
def modulePushforwardCompIso :
    (ofConstantCoefficient h Λ).modulePushforward ⋙
      (ofConstantCoefficient f Λ).modulePushforward ≅
      (ToposHom.comp (ofConstantCoefficient h Λ)
        (ofConstantCoefficient f Λ)).modulePushforward :=
  NatIso.ofComponents
    (fun M ↦
      moduleIsoOfUnderlying Λ Y ((modulePushforwardCompUnderlyingIso f Λ h).app M))
    (fun {M N} (φ : M ⟶ N) ↦ modulePushforwardCompIso_naturality f Λ h φ)

/-- Module inverse image along a composite scheme morphism is the composite of the
individual inverse images. -/
def modulePullbackCompIso :
    (ofConstantCoefficient f Λ).modulePullback ⋙
      (ofConstantCoefficient h Λ).modulePullback ≅
      (ToposHom.comp (ofConstantCoefficient h Λ)
        (ofConstantCoefficient f Λ)).modulePullback :=
  Adjunction.leftAdjointCompIso
    (moduleAdjunction (ofConstantCoefficient f Λ))
    (moduleAdjunction (ofConstantCoefficient h Λ))
    (moduleAdjunction
      (ToposHom.comp (ofConstantCoefficient h Λ) (ofConstantCoefficient f Λ)))
    (modulePushforwardCompIso f Λ h)

variable [(ofConstantCoefficient h Λ).modulePullback.Additive]
variable [(ToposHom.comp (ofConstantCoefficient h Λ)
    (ofConstantCoefficient f Λ)).modulePullback.Additive]
variable [(ofConstantCoefficient h Λ).HasModulePullbackDerived]
variable [(ToposHom.comp (ofConstantCoefficient h Λ)
    (ofConstantCoefficient f Λ)).HasModulePullbackDerived]
variable [(Functor.Homotopy.toDerived
    (ofConstantCoefficient f Λ).modulePullback).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso _ (up ℤ))]
variable [(Functor.Homotopy.toDerived
    (ofConstantCoefficient h Λ).modulePullback).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso _ (up ℤ))]
variable [(Functor.Homotopy.toDerived
    (ToposHom.comp (ofConstantCoefficient h Λ)
      (ofConstantCoefficient f Λ)).modulePullback).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso _ (up ℤ))]

/-- The homotopy-to-derived functor of a composite pullback identifies with the iterated
homotopy-level pullback model. -/
def modulePullbackToDerivedCompIso :
    modulePullbackToDerived
        (ToposHom.comp (ofConstantCoefficient h Λ) (ofConstantCoefficient f Λ)) ≅
      (ofConstantCoefficient f Λ).modulePullback.mapHomotopyCategory (up ℤ) ⋙
        modulePullbackToDerived (ofConstantCoefficient h Λ) :=
  Functor.LeftDerived.Homotopy.Composition.toDerivedIso
    (ofConstantCoefficient h Λ).modulePullback
    (ofConstantCoefficient f Λ).modulePullback
    (ToposHom.comp (ofConstantCoefficient h Λ)
      (ofConstantCoefficient f Λ)).modulePullback
    (modulePullbackCompIso f Λ h).symm

/-- Canonical comparison from iterated derived pullback to derived pullback along the
composite. Invertibility is an extra hypothesis. -/
def modulePullbackDerivedCompComparison :
    modulePullbackDerived (ofConstantCoefficient f Λ) ⋙
        modulePullbackDerived (ofConstantCoefficient h Λ) ⟶
      modulePullbackDerived
        (ToposHom.comp (ofConstantCoefficient h Λ) (ofConstantCoefficient f Λ)) :=
  Functor.LeftDerived.Homotopy.Composition.comparison
    (ofConstantCoefficient h Λ).modulePullback
    (ofConstantCoefficient f Λ).modulePullback
    (ToposHom.comp (ofConstantCoefficient h Λ)
      (ofConstantCoefficient f Λ)).modulePullback
    (modulePullbackCompIso f Λ h).symm

/-- Derived inverse image along a composite is the composite of the derived inverse
images, once the canonical comparison is invertible. -/
def modulePullbackDerivedCompIso
    [IsIso (modulePullbackDerivedCompComparison f Λ h)] :
    modulePullbackDerived (ofConstantCoefficient f Λ) ⋙
        modulePullbackDerived (ofConstantCoefficient h Λ) ≅
      modulePullbackDerived
        (ToposHom.comp (ofConstantCoefficient h Λ) (ofConstantCoefficient f Λ)) :=
  asIso (modulePullbackDerivedCompComparison f Λ h)

end CompAlong

variable {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
variable [HasWeakSheafify (topology X') CommRingCat.{v}]
variable [HasWeakSheafify (topology Y') CommRingCat.{v}]
variable [HasWeakSheafify (topology X') RingCat.{v}]
variable [HasWeakSheafify (topology Y') RingCat.{v}]
variable [HasWeakSheafify (topology X') (Type v)]
variable [HasWeakSheafify (topology Y') (Type v)]
variable [(topology X').HasSheafCompose (forget₂ CommRingCat.{v} RingCat.{v})]
variable [(topology Y').HasSheafCompose (forget₂ CommRingCat.{v} RingCat.{v})]
variable [(topology X').HasSheafCompose (CategoryTheory.forget RingCat.{v})]
variable [(topology Y').HasSheafCompose (CategoryTheory.forget RingCat.{v})]
variable [(topology X').PreservesSheafification (forget₂ CommRingCat.{v} RingCat.{v})]
variable [(topology Y').PreservesSheafification (forget₂ CommRingCat.{v} RingCat.{v})]
variable [(topology X').PreservesSheafification (CategoryTheory.forget RingCat.{v})]
variable [(topology Y').PreservesSheafification (CategoryTheory.forget RingCat.{v})]
variable [HasGlobalSectionsFunctor (topology X') (Type v)]
variable [HasGlobalSectionsFunctor (topology Y') (Type v)]
variable [∀ P : Y.ProEtᵒᵖ ⥤ Type v, (baseChange g).op.HasLeftKanExtension P]
variable [PreservesFiniteLimits
    ((baseChange g).sheafPullback (Type v) (topology Y) (topology Y'))]
variable [∀ P : Y'.ProEtᵒᵖ ⥤ Type v, (baseChange f').op.HasLeftKanExtension P]
variable [PreservesFiniteLimits
    ((baseChange f').sheafPullback (Type v) (topology Y') (topology X'))]
variable [∀ P : X.ProEtᵒᵖ ⥤ Type v, (baseChange g').op.HasLeftKanExtension P]
variable [PreservesFiniteLimits
    ((baseChange g').sheafPullback (Type v) (topology X) (topology X'))]
variable [(SheafOfModules.restrictScalars
    (ofConstantCoefficient g Λ).structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars
    (ofConstantCoefficient f' Λ).structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars
    (ofConstantCoefficient g' Λ).structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars
    (ToposHom.comp (ofConstantCoefficient g' Λ)
      (ofConstantCoefficient f Λ)).structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars
    (ToposHom.comp (ofConstantCoefficient f' Λ)
      (ofConstantCoefficient g Λ)).structureMap).IsRightAdjoint]
variable [(baseChange f ⋙ baseChange g').IsContinuous (topology Y) (topology X')]
variable [(baseChange g ⋙ baseChange f').IsContinuous (topology Y) (topology X')]

/-- After forgetting to type-valued sheaves, the two composite direct images of a
cartesian square agree via pro-étale base change. -/
def cartesianPushforwardUnderlyingIso (h_cart : IsPullback g' f' f g) :
    (ToposHom.comp (ofConstantCoefficient g' Λ)
          (ofConstantCoefficient f Λ)).modulePushforward ⋙
        ToInternal.underlying
          (ofCommRingSheaf (topology Y)
            (constantCoefficientRing Y Λ)).structureSheaf ≅
      (ToposHom.comp (ofConstantCoefficient f' Λ)
          (ofConstantCoefficient g Λ)).modulePushforward ⋙
        ToInternal.underlying
          (ofCommRingSheaf (topology Y)
            (constantCoefficientRing Y Λ)).structureSheaf :=
  ModulePushforward.forgetIso
      (ToposHom.comp (ofConstantCoefficient g' Λ) (ofConstantCoefficient f Λ)) ≪≫
    Functor.isoWhiskerLeft
      (ToInternal.underlying
        (ofCommRingSheaf (topology X')
          (constantCoefficientRing X' Λ)).structureSheaf)
      (Functor.sheafPushforwardContinuousIso
        (baseChangeSquareIso f g f' g' h_cart) (Type v)
        (topology Y) (topology X')) ≪≫
    (ModulePushforward.forgetIso
      (ToposHom.comp (ofConstantCoefficient f' Λ)
        (ofConstantCoefficient g Λ))).symm

/-- Naturality of the cartesian type-valued direct-image comparison after lifting to
module sheaves. -/
theorem cartesianPushforwardIso_naturality (h_cart : IsPullback g' f' f g)
    {M N :
      SheafOfModules.{v}
        (ofCommRingSheaf (topology X') (constantCoefficientRing X' Λ)).structureSheaf}
    (φ : M ⟶ N) :
    (ToposHom.comp (ofConstantCoefficient g' Λ)
            (ofConstantCoefficient f Λ)).modulePushforward.map φ ≫
        (moduleIsoOfUnderlying Λ Y
          ((cartesianPushforwardUnderlyingIso f Λ g f' g' h_cart).app N)).hom =
      (moduleIsoOfUnderlying Λ Y
          ((cartesianPushforwardUnderlyingIso f Λ g f' g' h_cart).app M)).hom ≫
        (ToposHom.comp (ofConstantCoefficient f' Λ)
            (ofConstantCoefficient g Λ)).modulePushforward.map φ :=
  sorry

/-- The two composite module direct images of a cartesian square are canonically
isomorphic. -/
def cartesianPushforwardIso (h_cart : IsPullback g' f' f g) :
    (ToposHom.comp (ofConstantCoefficient g' Λ)
        (ofConstantCoefficient f Λ)).modulePushforward ≅
      (ToposHom.comp (ofConstantCoefficient f' Λ)
        (ofConstantCoefficient g Λ)).modulePushforward :=
  NatIso.ofComponents
    (fun M ↦
      moduleIsoOfUnderlying Λ Y
        ((cartesianPushforwardUnderlyingIso f Λ g f' g' h_cart).app M))
    (fun {M N} (φ : M ⟶ N) ↦
      cartesianPushforwardIso_naturality f Λ g f' g' h_cart φ)

/-- The two composite module inverse images of a cartesian square are canonically
isomorphic. -/
def cartesianPullbackIso (h_cart : IsPullback g' f' f g) :
    (ToposHom.comp (ofConstantCoefficient f' Λ)
        (ofConstantCoefficient g Λ)).modulePullback ≅
      (ToposHom.comp (ofConstantCoefficient g' Λ)
        (ofConstantCoefficient f Λ)).modulePullback :=
  (conjugateIsoEquiv
      (moduleAdjunction
        (ToposHom.comp (ofConstantCoefficient g' Λ) (ofConstantCoefficient f Λ)))
      (moduleAdjunction
        (ToposHom.comp (ofConstantCoefficient f' Λ)
          (ofConstantCoefficient g Λ)))).symm
    (cartesianPushforwardIso f Λ g f' g' h_cart)

variable [(ofConstantCoefficient g Λ).modulePullback.Additive]
variable [(ofConstantCoefficient f' Λ).modulePullback.Additive]
variable [(ofConstantCoefficient g' Λ).modulePullback.Additive]
variable [(ToposHom.comp (ofConstantCoefficient f' Λ)
    (ofConstantCoefficient g Λ)).modulePullback.Additive]
variable [(ToposHom.comp (ofConstantCoefficient g' Λ)
    (ofConstantCoefficient f Λ)).modulePullback.Additive]
variable [(ofConstantCoefficient g Λ).HasModulePullbackDerived]
variable [(ofConstantCoefficient f' Λ).HasModulePullbackDerived]
variable [(ofConstantCoefficient g' Λ).HasModulePullbackDerived]
variable [(ofConstantCoefficient f' Λ).HasModulePushforwardDerived]
variable [(ToposHom.comp (ofConstantCoefficient f' Λ)
    (ofConstantCoefficient g Λ)).HasModulePullbackDerived]
variable [(ToposHom.comp (ofConstantCoefficient g' Λ)
    (ofConstantCoefficient f Λ)).HasModulePullbackDerived]
variable [(Functor.Homotopy.toDerived
    (ofConstantCoefficient g Λ).modulePullback).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso _ (up ℤ))]
variable [(Functor.Homotopy.toDerived
    (ofConstantCoefficient f' Λ).modulePullback).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso _ (up ℤ))]
variable [(Functor.Homotopy.toDerived
    (ofConstantCoefficient g' Λ).modulePullback).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso _ (up ℤ))]
variable [(Functor.Homotopy.toDerived
    (ToposHom.comp (ofConstantCoefficient f' Λ)
      (ofConstantCoefficient g Λ)).modulePullback).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso _ (up ℤ))]
variable [(Functor.Homotopy.toDerived
    (ToposHom.comp (ofConstantCoefficient g' Λ)
      (ofConstantCoefficient f Λ)).modulePullback).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso _ (up ℤ))]
variable [Adjunction.TotalDerived.HasPair
    (G := (ofConstantCoefficient f' Λ).modulePullback.mapHomotopyCategory (up ℤ))
    (F := (ofConstantCoefficient f' Λ).modulePushforward.mapHomotopyCategory (up ℤ))
    (ModuleQis (ofCommRingSheaf (topology Y') (constantCoefficientRing Y' Λ)))
    (ModuleQis (ofCommRingSheaf (topology X') (constantCoefficientRing X' Λ)))
    (L1 :=
      moduleLocalization
        (ofCommRingSheaf (topology Y') (constantCoefficientRing Y' Λ)))
    (L2 :=
      moduleLocalization
        (ofCommRingSheaf (topology X') (constantCoefficientRing X' Λ)))]

variable [HasWeakSheafify (topology X') AddCommGrpCat.{v}]
variable [HasWeakSheafify (topology Y') AddCommGrpCat.{v}]
variable [(topology X').WEqualsLocallyBijective RingCat.{v}]
variable [(topology Y').WEqualsLocallyBijective RingCat.{v}]
variable [(topology X').WEqualsLocallyBijective AddCommGrpCat.{v}]
variable [(topology Y').WEqualsLocallyBijective AddCommGrpCat.{v}]
variable [(topology X').HasSheafCompose (forget₂ RingCat.{v} AddCommGrpCat.{v})]
variable [(topology Y').HasSheafCompose (forget₂ RingCat.{v} AddCommGrpCat.{v})]
variable [(ofConstantCoefficient g Λ).HasModulePushforwardDerived]
variable [Adjunction.TotalDerived.HasPair
    (G := (ofConstantCoefficient g Λ).modulePullback.mapHomotopyCategory (up ℤ))
    (F := (ofConstantCoefficient g Λ).modulePushforward.mapHomotopyCategory (up ℤ))
    (ModuleQis (ofCommRingSheaf (topology Y) (constantCoefficientRing Y Λ)))
    (ModuleQis (ofCommRingSheaf (topology Y') (constantCoefficientRing Y' Λ)))
    (L1 :=
      moduleLocalization
        (ofCommRingSheaf (topology Y) (constantCoefficientRing Y Λ)))
    (L2 :=
      moduleLocalization
        (ofCommRingSheaf (topology Y') (constantCoefficientRing Y' Λ)))]
variable [∀ P : Y.ProEtᵒᵖ ⥤ Type v, (baseChange (g' ≫ f)).op.HasLeftKanExtension P]
variable [PreservesFiniteLimits
    ((baseChange (g' ≫ f)).sheafPullback (Type v) (topology Y) (topology X'))]
variable [∀ P : Y.ProEtᵒᵖ ⥤ Type v, (baseChange (f' ≫ g)).op.HasLeftKanExtension P]
variable [PreservesFiniteLimits
    ((baseChange (f' ≫ g)).sheafPullback (Type v) (topology Y) (topology X'))]
variable [(SheafOfModules.restrictScalars
    (ofConstantCoefficient (g' ≫ f) Λ).structureMap).IsRightAdjoint]
variable [(SheafOfModules.restrictScalars
    (ofConstantCoefficient (f' ≫ g) Λ).structureMap).IsRightAdjoint]
variable [HasWeakSheafify (topology X') (ModuleCat.{v} Λ)]
variable [HasWeakSheafify (topology Y') (ModuleCat.{v} Λ)]
variable [Abelian (Sheaf (topology X') (ModuleCat.{v} Λ))]
variable [Abelian (Sheaf (topology Y') (ModuleCat.{v} Λ))]
variable [HasDerivedCategory (Sheaf (topology X') (ModuleCat.{v} Λ))]
variable [HasDerivedCategory (Sheaf (topology Y') (ModuleCat.{v} Λ))]
variable [LocallySmall
    (SheafOfModules (ringSheafOfComm (constantCoefficientRing X' Λ)))]
variable [LocallySmall
    (SheafOfModules (ringSheafOfComm (constantCoefficientRing Y' Λ)))]
variable [WellPowered
    (SheafOfModules (ringSheafOfComm (constantCoefficientRing X' Λ)))]
variable [WellPowered
    (SheafOfModules (ringSheafOfComm (constantCoefficientRing Y' Λ)))]
variable [∀ U : X'.ProEt, HasWeakSheafify ((topology X').over U) AddCommGrpCat.{v}]
variable [∀ U : X'.ProEt, ((topology X').over U).WEqualsLocallyBijective AddCommGrpCat.{v}]
variable [∀ U : Y'.ProEt, HasWeakSheafify ((topology Y').over U) AddCommGrpCat.{v}]
variable [∀ U : Y'.ProEt, ((topology Y').over U).WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- Derived inverse images of the two composite morphisms of a cartesian square are
identified by transporting the underived cartesian iso. -/
def modulePullbackDerivedCartesianIso (h_cart : IsPullback g' f' f g) :
    modulePullbackDerived
        (ToposHom.comp (ofConstantCoefficient f' Λ) (ofConstantCoefficient g Λ)) ≅
      modulePullbackDerived
        (ToposHom.comp (ofConstantCoefficient g' Λ) (ofConstantCoefficient f Λ)) :=
  Functor.LeftDerived.mapNatIso
    (moduleLocalization
      (ofCommRingSheaf (topology Y) (constantCoefficientRing Y Λ)))
    (ModuleQis (ofCommRingSheaf (topology Y) (constantCoefficientRing Y Λ)))
    (Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryIso (cartesianPullbackIso f Λ g f' g' h_cart))
      (moduleLocalization
        (ofCommRingSheaf (topology X') (constantCoefficientRing X' Λ))))

/-- Derived inverse images of a cartesian square of schemes form a commutative
square. -/
def modulePullbackDerivedSquareIso (h_cart : IsPullback g' f' f g)
    [IsIso (modulePullbackDerivedCompComparison g Λ f')]
    [IsIso (modulePullbackDerivedCompComparison f Λ g')] :
    modulePullbackDerived (ofConstantCoefficient g Λ) ⋙
        modulePullbackDerived (ofConstantCoefficient f' Λ) ≅
      modulePullbackDerived (ofConstantCoefficient f Λ) ⋙
        modulePullbackDerived (ofConstantCoefficient g' Λ) :=
  modulePullbackDerivedCompIso g Λ f' ≪≫
    modulePullbackDerivedCartesianIso f Λ g f' g' h_cart ≪≫
    (modulePullbackDerivedCompIso f Λ g').symm

/-- The completed derived base-change morphism
`Lg_comp^* Rf_* K ⟶ Rf'_* L(g')_comp^* K` of a cartesian square. -/
def completedDerivedBaseChangeHom (h_cart : IsPullback g' f' f g) (I : Ideal Λ)
    [(coefficientIdeal X Λ I :
        ringedSiteModuleCategory (topology X) (constantCoefficientRing X Λ)).IsFiniteType]
    [(coefficientIdeal X' Λ I :
        ringedSiteModuleCategory (topology X') (constantCoefficientRing X' Λ)).IsFiniteType]
    [(coefficientIdeal Y' Λ I :
        ringedSiteModuleCategory (topology Y') (constantCoefficientRing Y' Λ)).IsFiniteType]
    [IsIso (modulePullbackDerivedCompComparison g Λ f')]
    [IsIso (modulePullbackDerivedCompComparison f Λ g')]
    (K :
      (derivedCompleteObjectProperty (coefficientIdeal X Λ I)).FullSubcategory) :
    (completedPullback g Λ I).obj ((completedPushforward f Λ I).obj K) ⟶
      (completedPushforward f' Λ I).obj ((completedPullback g' Λ I).obj K) :=
  (Completion.homEquiv (coefficientIdeal Y' Λ I)
      ((modulePullbackDerived (ofConstantCoefficient g Λ)).obj
        ((modulePushforwardDerived (ofConstantCoefficient f Λ)).obj K.obj))
      ((completedPushforward f' Λ I).obj
        ((completedPullback g' Λ I).obj K))).symm
    (derivedBaseChangeMap
        (modulePullbackDerived (ofConstantCoefficient f Λ))
        (modulePullbackDerived (ofConstantCoefficient f' Λ))
        (modulePullbackDerived (ofConstantCoefficient g Λ))
        (modulePullbackDerived (ofConstantCoefficient g' Λ))
        (modulePushforwardDerived (ofConstantCoefficient f Λ))
        (modulePushforwardDerived (ofConstantCoefficient f' Λ))
        (constantModuleDerivedAdjunction f Λ)
        (constantModuleDerivedAdjunction f' Λ)
        (modulePullbackDerivedSquareIso f Λ g f' g' h_cart) K.obj ≫
      (modulePushforwardDerived (ofConstantCoefficient f' Λ)).map
        ((Completion.unit (coefficientIdeal X' Λ I)).app
          ((modulePullbackDerived (ofConstantCoefficient g' Λ)).obj K.obj)))

/-- A morphism is the completed derived base-change map when its adjunct under
derived completion is the unbounded mate followed by the completion unit. -/
def IsCompletedDerivedBaseChangeMap (h_cart : IsPullback g' f' f g) (I : Ideal Λ)
    [(coefficientIdeal X Λ I :
        ringedSiteModuleCategory (topology X) (constantCoefficientRing X Λ)).IsFiniteType]
    [(coefficientIdeal X' Λ I :
        ringedSiteModuleCategory (topology X') (constantCoefficientRing X' Λ)).IsFiniteType]
    [(coefficientIdeal Y' Λ I :
        ringedSiteModuleCategory (topology Y') (constantCoefficientRing Y' Λ)).IsFiniteType]
    [IsIso (modulePullbackDerivedCompComparison g Λ f')]
    [IsIso (modulePullbackDerivedCompComparison f Λ g')]
    (K :
      (derivedCompleteObjectProperty (coefficientIdeal X Λ I)).FullSubcategory)
    (η :
      (completedPullback g Λ I).obj ((completedPushforward f Λ I).obj K) ⟶
        (completedPushforward f' Λ I).obj
          ((completedPullback g' Λ I).obj K)) : Prop :=
  (Completion.homEquiv (coefficientIdeal Y' Λ I)
      ((modulePullbackDerived (ofConstantCoefficient g Λ)).obj
        ((modulePushforwardDerived (ofConstantCoefficient f Λ)).obj K.obj))
      ((completedPushforward f' Λ I).obj
        ((completedPullback g' Λ I).obj K))) η =
    derivedBaseChangeMap
        (modulePullbackDerived (ofConstantCoefficient f Λ))
        (modulePullbackDerived (ofConstantCoefficient f' Λ))
        (modulePullbackDerived (ofConstantCoefficient g Λ))
        (modulePullbackDerived (ofConstantCoefficient g' Λ))
        (modulePushforwardDerived (ofConstantCoefficient f Λ))
        (modulePushforwardDerived (ofConstantCoefficient f' Λ))
        (constantModuleDerivedAdjunction f Λ)
        (constantModuleDerivedAdjunction f' Λ)
        (modulePullbackDerivedSquareIso f Λ g f' g' h_cart) K.obj ≫
      (modulePushforwardDerived (ofConstantCoefficient f' Λ)).map
        ((Completion.unit (coefficientIdeal X' Λ I)).app
          ((modulePullbackDerived (ofConstantCoefficient g' Λ)).obj K.obj))

/-- The canonical comparison satisfies the completed base-change specification. -/
theorem completedDerivedBaseChangeHom_isMap (h_cart : IsPullback g' f' f g)
    (I : Ideal Λ)
    [(coefficientIdeal X Λ I :
        ringedSiteModuleCategory (topology X) (constantCoefficientRing X Λ)).IsFiniteType]
    [(coefficientIdeal X' Λ I :
        ringedSiteModuleCategory (topology X') (constantCoefficientRing X' Λ)).IsFiniteType]
    [(coefficientIdeal Y' Λ I :
        ringedSiteModuleCategory (topology Y') (constantCoefficientRing Y' Λ)).IsFiniteType]
    [IsIso (modulePullbackDerivedCompComparison g Λ f')]
    [IsIso (modulePullbackDerivedCompComparison f Λ g')]
    (K :
      (derivedCompleteObjectProperty (coefficientIdeal X Λ I)).FullSubcategory) :
    IsCompletedDerivedBaseChangeMap f Λ g f' g' h_cart I K
      (completedDerivedBaseChangeHom f Λ g f' g' h_cart I K) := sorry

/-- Transposing the completed comparison across derived completion recovers the
unbounded mate followed by the completion unit. -/
theorem completedDerivedBaseChangeHom_spec (h_cart : IsPullback g' f' f g)
    (I : Ideal Λ)
    [(coefficientIdeal X Λ I :
        ringedSiteModuleCategory (topology X) (constantCoefficientRing X Λ)).IsFiniteType]
    [(coefficientIdeal X' Λ I :
        ringedSiteModuleCategory (topology X') (constantCoefficientRing X' Λ)).IsFiniteType]
    [(coefficientIdeal Y' Λ I :
        ringedSiteModuleCategory (topology Y') (constantCoefficientRing Y' Λ)).IsFiniteType]
    [IsIso (modulePullbackDerivedCompComparison g Λ f')]
    [IsIso (modulePullbackDerivedCompComparison f Λ g')]
    (K :
      (derivedCompleteObjectProperty (coefficientIdeal X Λ I)).FullSubcategory) :
    (Completion.homEquiv (coefficientIdeal Y' Λ I)
        ((modulePullbackDerived (ofConstantCoefficient g Λ)).obj
          ((modulePushforwardDerived (ofConstantCoefficient f Λ)).obj K.obj))
        ((completedPushforward f' Λ I).obj
          ((completedPullback g' Λ I).obj K)))
      (completedDerivedBaseChangeHom f Λ g f' g' h_cart I K) =
      derivedBaseChangeMap
          (modulePullbackDerived (ofConstantCoefficient f Λ))
          (modulePullbackDerived (ofConstantCoefficient f' Λ))
          (modulePullbackDerived (ofConstantCoefficient g Λ))
          (modulePullbackDerived (ofConstantCoefficient g' Λ))
          (modulePushforwardDerived (ofConstantCoefficient f Λ))
          (modulePushforwardDerived (ofConstantCoefficient f' Λ))
          (constantModuleDerivedAdjunction f Λ)
          (constantModuleDerivedAdjunction f' Λ)
          (modulePullbackDerivedSquareIso f Λ g f' g' h_cart) K.obj ≫
        (modulePushforwardDerived (ofConstantCoefficient f' Λ)).map
          ((Completion.unit (coefficientIdeal X' Λ I)).app
            ((modulePullbackDerived (ofConstantCoefficient g' Λ)).obj K.obj)) :=
  sorry

/-- A morphism satisfying the completed base-change specification equals the
canonical comparison. -/
theorem IsCompletedDerivedBaseChangeMap.eq_hom (h_cart : IsPullback g' f' f g)
    (I : Ideal Λ)
    [(coefficientIdeal X Λ I :
        ringedSiteModuleCategory (topology X) (constantCoefficientRing X Λ)).IsFiniteType]
    [(coefficientIdeal X' Λ I :
        ringedSiteModuleCategory (topology X') (constantCoefficientRing X' Λ)).IsFiniteType]
    [(coefficientIdeal Y' Λ I :
        ringedSiteModuleCategory (topology Y') (constantCoefficientRing Y' Λ)).IsFiniteType]
    [IsIso (modulePullbackDerivedCompComparison g Λ f')]
    [IsIso (modulePullbackDerivedCompComparison f Λ g')]
    (K :
      (derivedCompleteObjectProperty (coefficientIdeal X Λ I)).FullSubcategory)
    {η :
      (completedPullback g Λ I).obj ((completedPushforward f Λ I).obj K) ⟶
        (completedPushforward f' Λ I).obj
          ((completedPullback g' Λ I).obj K)}
    (hη : IsCompletedDerivedBaseChangeMap f Λ g f' g' h_cart I K η) :
    η = completedDerivedBaseChangeHom f Λ g f' g' h_cart I K := sorry

end AlgebraicGeometry.Scheme.ProEt
