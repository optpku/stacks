module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.Naturality
public import ReasLib.CategoryTheory.Functor.Derived.Composition.Right
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.EtaleBaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Homotopy
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.LowerShriek
public import ReasLib.Algebra.Homology.CochainComplex.KInjective.Adjunction
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-! # Derived étale base change for module pushforward

For a cartesian square with étale vertical maps, derived module pushforward
commutes with étale restriction through the canonical Beck--Chevalley comparison.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits CategoryTheory.Functor
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}}
variable {X' X Y' Y : AlgebraicSpace S}
variable {h : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
variable [Etale g] [Etale h]

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

private theorem rightDerived_precompose_iso
    {C D H : Type*} [Category C] [Category D] [Category H]
    {L : C ⥤ D} {F G : C ⥤ H} {RF : D ⥤ H}
    (W : MorphismProperty C) [L.IsLocalization W]
    (α : F ⟶ L ⋙ RF) [RF.IsRightDerivedFunctor α W] (e : G ≅ F) :
    RF.IsRightDerivedFunctor (e.hom ≫ α) W := by
  refine ⟨(Functor.isLeftKanExtension_iff_of_iso₂
    (e.hom ≫ α) α e (Iso.refl RF) (by simp)).2 ?_⟩
  exact Functor.IsRightDerivedFunctor.isLeftKanExtension RF α W

set_option backward.isDefEq.respectTransparency false in
/-- The K-injective derived functor of the underived right composite is a right-derived
model of that composite. -/
instance derivedRestrictPushforwardComposite_isRightDerived :
    (modulesHomotopyFunctor (restrictFunctor h ⋙ pushforward f')).IsRightDerivedFunctor
      derivedRestrictPushforwardCompositeUnit
      (@HomotopyCategory.quasiIso X.Modules _ ℤ (up ℤ) X.modulesAbelian.toPreadditive
        inferInstance) :=
  by
    let e : modulesMapHomotopy (restrictFunctor h) ⋙
        modulesHomotopyToDerived (pushforward f') ≅
        modulesHomotopyToDerived (restrictFunctor h ⋙ pushforward f') :=
      associator (modulesMapHomotopy (restrictFunctor h))
        (modulesMapHomotopy (pushforward f')) (modulesQh Y') ≪≫
        isoWhiskerRight
          (mapHomotopyCategoryCompIso (Iso.refl (restrictFunctor h ⋙ pushforward f'))
            (up ℤ)) (modulesQh Y')
    simpa only [e, derivedRestrictPushforwardCompositeUnit, Iso.trans_hom,
      Category.assoc] using
      rightDerived_precompose_iso (HomotopyCategory.quasiIso X.Modules (up ℤ))
        (modulesHomotopyUnit (restrictFunctor h ⋙ pushforward f')) e

/-- Right-derived composition comparison
`R((f_* -)|_{Y'}) ⟶ Rf_* ⋙ (-)|_{Y'}`. -/
def derivedPushforwardRestrictComparison :
    modulesHomotopyFunctor (pushforward f ⋙ restrictFunctor g) ⟶
      moduleDerivedPushforward f ⋙ restrictFunctorDerived g :=
  @RightDerived.Composition.comparisonOfModels
    (modulesHomotopy X) (modulesHomotopy Y) (ModuleDerived Y')
    (ModuleDerived X) (ModuleDerived Y)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (modulesMapHomotopy (pushforward f))
    (modulesHomotopyToDerived (restrictFunctor g))
    (modulesQh X) (modulesQh Y)
    (moduleDerivedPushforward f) (restrictFunctorDerived g)
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
        moduleDerivedPushforward f ⋙ restrictFunctorDerived g) :=
  sorry

/-- Right-derived composition comparison
`R(f'_*((-)|_{X'})) ⟶ (-)|_{X'} ⋙ Rf'_*`. -/
def derivedRestrictPushforwardComparison :
    modulesHomotopyFunctor (restrictFunctor h ⋙ pushforward f') ⟶
      restrictFunctorDerived h ⋙ moduleDerivedPushforward f' :=
  @RightDerived.Composition.comparisonOfModels
    (modulesHomotopy X) (modulesHomotopy X') (ModuleDerived Y')
    (ModuleDerived X) (ModuleDerived X')
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (modulesMapHomotopy (restrictFunctor h))
    (modulesHomotopyToDerived (pushforward f'))
    (modulesQh X) (modulesQh X')
    (restrictFunctorDerived h) (moduleDerivedPushforward f')
    (modulesHomotopyFunctor (restrictFunctor h ⋙ pushforward f'))
    (@HomotopyCategory.quasiIso X.Modules _ ℤ (up ℤ) X.modulesAbelian.toPreadditive
      inferInstance)
    (modulesRestrictFactorshInv h)
    (modulesHomotopyUnit (pushforward f'))
    derivedRestrictPushforwardCompositeUnit
    inferInstance inferInstance

set_option backward.isDefEq.respectTransparency false in
private theorem cochainUnit_isIso_of_isKInjective
    {P Q : AlgebraicSpace S} (F : P.Modules ⥤ Q.Modules) [F.Additive]
    (K : CochainComplex P.Modules ℤ) [K.IsKInjective] :
    IsIso ((Functor.RightDerived.KInjective.unit.{u} F).app K) := by
    let a : K ⟶ (CochainComplex.KInjectiveResolution.Construction.replacement.{u}
        P.Modules).obj K :=
      (CochainComplex.KInjectiveResolution.Construction.augmentation.{u} P.Modules).app K
    have hReplacement : ((CochainComplex.KInjectiveResolution.Construction.replacement.{u}
      P.Modules).obj K).IsKInjective :=
      CochainComplex.KInjectiveResolution.Construction.replacement_isKInjective P.Modules K
    have ha : QuasiIso a :=
      CochainComplex.KInjectiveResolution.Construction.augmentation_quasiIso P.Modules K
    have hq : IsIso ((HomotopyCategory.quotient P.Modules (up ℤ)).map a) :=
      HomotopyCategory.quotient_inverts_homotopyEquivalences _ _ a
        ((CochainComplex.IsKInjective.quasiIso_iff a).1 ha)
    have hm : IsIso (((HomotopyCategory.quotient P.Modules (up ℤ)) ⋙
      Functor.Homotopy.toDerived F).map a) := by
      change IsIso ((Functor.Homotopy.toDerived F).map
        ((HomotopyCategory.quotient P.Modules (up ℤ)).map a))
      infer_instance
    have hm' : IsIso ((Functor.KInjectiveModel.ordinaryCochain F).map a) :=
      (NatIso.isIso_map_iff (Functor.Homotopy.cochainIso F) a).1 hm
    have hunit : IsIso ((Functor.KInjectiveModel.unit.{u} F).app K) := by
      dsimp [Functor.KInjectiveModel.unit]
      change IsIso (𝟙 _ ≫ (Functor.KInjectiveModel.ordinaryCochain F).map a ≫ _)
      infer_instance
    -- The explicit certificate fixes the supplied cochain unit for native uniqueness.
    have hDerived : (Functor.RightDerived.KInjective.functor.{u} F).IsRightDerivedFunctor
        (Functor.RightDerived.KInjective.unit.{u} F)
        (HomologicalComplex.quasiIso P.Modules (up ℤ)) :=
      Functor.RightDerived.KInjective.isRightDerived F
    let e := Functor.KInjectiveModel.isoOfModel.{u} F
      (Functor.RightDerived.KInjective.functor.{u} F)
      (Functor.RightDerived.KInjective.unit.{u} F)
    have he : (Functor.KInjectiveModel.unit.{u} F).app K ≫
        e.hom.app (DerivedCategory.Q.obj K) =
        (Functor.RightDerived.KInjective.unit.{u} F).app K := by
      simpa [e, Functor.KInjectiveModel.isoOfModel, Functor.rightDerivedUnique,
        Functor.rightDerivedNatIso, Functor.rightDerivedNatTrans] using
        (Functor.KInjectiveModel.derived.{u} F).rightDerived_fac_app
          (Functor.KInjectiveModel.unit.{u} F)
          (HomologicalComplex.quasiIso P.Modules (up ℤ))
          (Functor.RightDerived.KInjective.functor.{u} F)
          (𝟙 _ ≫ Functor.RightDerived.KInjective.unit.{u} F) K
    rw [← he]
    infer_instance


set_option backward.isDefEq.respectTransparency false in
private theorem homotopyUnit_isIso_of_isKInjective
    {P Q : AlgebraicSpace S} (F : P.Modules ⥤ Q.Modules) [F.Additive]
    (K : CochainComplex P.Modules ℤ) [K.IsKInjective] :
    IsIso ((modulesHomotopyUnit F).app
      ((HomotopyCategory.quotient P.Modules (up ℤ)).obj K)) := by
  have hc := cochainUnit_isIso_of_isKInjective F K
  simpa only [Functor.RightDerived.KInjective.unit,
    Functor.RightDerived.Homotopy.cochainUnit, NatTrans.comp_app,
    Functor.whiskerLeft_app, isIso_comp_left_iff, isIso_comp_right_iff] using hc

set_option backward.isDefEq.respectTransparency false in
/-- The right composition comparison is an isomorphism. -/
instance isIso_derivedRestrictPushforwardComparison :
    IsIso (derivedRestrictPushforwardComparison :
      modulesHomotopyFunctor (restrictFunctor h ⋙ pushforward f') ⟶
        restrictFunctorDerived h ⋙ moduleDerivedPushforward f') :=
  by
    rw [NatTrans.isIso_iff_isIso_app]
    intro E
    let K := (DerivedCategory.Q (C := X.Modules)).objPreimage E
    let I := (CochainComplex.KInjectiveResolution.Construction.replacement.{u}
      X.Modules).obj K
    have hI : I.IsKInjective :=
      CochainComplex.KInjectiveResolution.Construction.replacement_isKInjective X.Modules K
    let e : DerivedCategory.Q.obj I ≅ E :=
      (Functor.KInjectiveModel.inputAugmentationIso.{u} K).symm ≪≫
        (DerivedCategory.Q (C := X.Modules)).objObjPreimageIso E
    rw [← NatTrans.isIso_app_iff_of_iso derivedRestrictPushforwardComparison e]
    have hRestrict : CochainComplex.IsKInjective
        (((restrictFunctor h).mapHomologicalComplex (up ℤ)).obj I) :=
      CochainComplex.IsKInjective.mapHomologicalComplex_of_exactLeftAdjoint I
        (lowerShriekAdjunction h)
        ((exactFunctor_iff (lowerShriek h)).2 ⟨inferInstance, inferInstance⟩)
    have hG := homotopyUnit_isIso_of_isKInjective (pushforward f')
      (((restrictFunctor h).mapHomologicalComplex (up ℤ)).obj I)
    have hGF := homotopyUnit_isIso_of_isKInjective (restrictFunctor h ⋙ pushforward f') I
    have hαGF : IsIso ((derivedRestrictPushforwardCompositeUnit (h := h) (f' := f')).app
        ((HomotopyCategory.quotient X.Modules (up ℤ)).obj I)) := by
      dsimp only [derivedRestrictPushforwardCompositeUnit, NatTrans.comp_app]
      infer_instance
    have hαG : IsIso ((modulesHomotopyUnit (pushforward f')).app
        ((modulesMapHomotopy (restrictFunctor h)).obj
          ((HomotopyCategory.quotient X.Modules (up ℤ)).obj I))) := by
      exact hG
    have hc := RightDerived.Composition.comparisonOfModels_app_isIso
      (HomotopyCategory.quasiIso X.Modules (up ℤ))
      (modulesRestrictFactorshInv h) (modulesHomotopyUnit (pushforward f'))
      derivedRestrictPushforwardCompositeUnit
      ((HomotopyCategory.quotient X.Modules (up ℤ)).obj I)
    exact (NatTrans.isIso_app_iff_of_iso derivedRestrictPushforwardComparison
      ((DerivedCategory.quotientCompQhIso X.Modules).app I)).1 hc

/-- The derived étale Beck--Chevalley isomorphism of functors on `D(𝒪_X)`. -/
def derivedPushforwardEtaleBaseChangeNatIso (h_cart : IsPullback h f' f g) :
    moduleDerivedPushforward f ⋙ restrictFunctorDerived g ≅
      restrictFunctorDerived h ⋙ moduleDerivedPushforward f' :=
  (asIso derivedPushforwardRestrictComparison).symm ≪≫
    (@RightDerived.Homotopy.mapNatIso X.Modules _ X.modulesAbelian (modulesHasDerivedCategory X)
      Y'.Modules _ Y'.modulesAbelian (modulesHasDerivedCategory Y')
      (pushforward f ⋙ restrictFunctor g) (restrictFunctor h ⋙ pushforward f')
      inferInstance inferInstance inferInstance inferInstance
      (NatIso.ofComponents (fun F ↦ pushforwardEtaleBaseChangeIso h_cart F)
        (fun {F G} φ ↦ (pushforwardEtaleBaseChangeNatTrans h_cart).naturality φ))) ≪≫
      asIso derivedRestrictPushforwardComparison

/-- The canonical derived base-change morphism
`(Rf_* E)|_{Y'} ⟶ Rf'_*(E|_{X'})` in `D(𝒪_{Y'})`. -/
def derivedPushforwardEtaleBaseChangeHom (h_cart : IsPullback h f' f g)
    (E : ModuleDerived X) :
    (restrictFunctorDerived g).obj ((moduleDerivedPushforward f).obj E) ⟶
      (moduleDerivedPushforward f').obj ((restrictFunctorDerived h).obj E) :=
  (derivedPushforwardEtaleBaseChangeNatIso h_cart).hom.app E

/-- The derived étale base-change morphism is an isomorphism. -/
instance isIso_derivedPushforwardEtaleBaseChangeHom (h_cart : IsPullback h f' f g)
    (E : ModuleDerived X) :
    IsIso (derivedPushforwardEtaleBaseChangeHom h_cart E) := by
  change IsIso ((derivedPushforwardEtaleBaseChangeNatIso h_cart).hom.app E)
  infer_instance

/-- The identification `(Rf_* E)|_{Y'} ≅ Rf'_*(E|_{X'})` in `D(𝒪_{Y'})`. -/
def derivedPushforwardEtaleBaseChangeIso (h_cart : IsPullback h f' f g)
    (E : ModuleDerived X) :
    (restrictFunctorDerived g).obj ((moduleDerivedPushforward f).obj E) ≅
      (moduleDerivedPushforward f').obj ((restrictFunctorDerived h).obj E) :=
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

/-- Restriction of `Rf_* E` along étale `g : V ⟶ Y` is
identified with the derived pushforward of the restriction of `E` to `U = V ×_Y X`,
modelled as the mathlib pullback `X ×_Y V`. -/
def derivedPushforwardEtaleBaseChangeIso_of_hasPullback
    (f : X ⟶ Y) (g : V ⟶ Y)
    [Etale g] [HasPullback f g]
    (E : ModuleDerived X) :
    (restrictFunctorDerived g).obj ((moduleDerivedPushforward f).obj E) ≅
      (moduleDerivedPushforward (Limits.pullback.snd f g)).obj
        ((restrictFunctorDerived (Limits.pullback.fst f g)).obj E) :=
  derivedPushforwardEtaleBaseChangeIso (IsPullback.of_hasPullback f g) E

end AlgebraicGeometry.AlgebraicSpace.Modules

