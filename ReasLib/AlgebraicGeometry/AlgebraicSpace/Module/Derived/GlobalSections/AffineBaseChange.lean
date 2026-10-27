/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GlobalSections.MapToAffine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.AffineSpectrum
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.GlobalSections.Abelian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Adjunction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.BaseChange
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Adjunction
public import ReasLib.CategoryTheory.DerivedCategory.Functor.KInjectiveModel.Composition

/-! # Scalar-valued global sections and affine base change -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry ComplexShape

noncomputable section

set_option backward.privateInPublic true

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.AffineGlobalSections

/-- Derived global sections with coefficients supplied by an explicit morphism to an
affine scheme over the ambient base. -/
def functor {S : Scheme.{u}} {X : AlgebraicSpace S} {A : CommRingCat.{u}}
    {a : Spec A ⟶ S} (f : X ⟶ ofOver (Over.mk a)) :
    ModuleDerived X ⥤ DerivedCategory (ModuleCat.{u} A) :=
  moduleDerivedGlobalSections X ⋙
    ModuleCat.derivedRestrictionOfScalars (Hom.affineGlobalSectionsMap f).hom

/-- Underived global sections with the action induced by an affine-target morphism. -/
private abbrev underived {S : Scheme.{u}} {X : AlgebraicSpace S} {A : CommRingCat.{u}}
    {a : Spec A ⟶ S} (f : X ⟶ ofOver (Over.mk a)) : X.Modules ⥤ ModuleCat.{u} A :=
  moduleGlobalSectionsFunctor X ⋙
    ModuleCat.restrictScalars (Hom.affineGlobalSectionsMap f).hom

/-- The scalar-valued global-sections functor uses the same specified injective model
as global sections before exact scalar restriction. -/
private def modelIso {S : Scheme.{u}} {X : AlgebraicSpace S} {A : CommRingCat.{u}}
    {a : Spec A ⟶ S} (f : X ⟶ ofOver (Over.mk a)) :
    functor f ≅ KInjectiveModel.derived.{u} (underived f) :=
  isoWhiskerRight
      (@KInjectiveModel.isoOfModel.{u} _ _ _ _ _ _ _ _ _
        (moduleGlobalSectionsFunctor X) _ (moduleDerivedGlobalSections X)
        (moduleDerivedGlobalSections.unit X) (moduleDerivedGlobalSections.isRightDerived X)).symm
      (ModuleCat.derivedRestrictionOfScalars (Hom.affineGlobalSectionsMap f).hom) ≪≫
    KInjectiveModel.postcomposeIso (moduleGlobalSectionsFunctor X)
      (ModuleCat.restrictScalars (Hom.affineGlobalSectionsMap f).hom)

section Comparison

variable {S : Scheme.{u}} {A B : CommRingCat.{u}} {φ : A ⟶ B}
variable {a : Spec A ⟶ S} {b : Spec B ⟶ S} {w : Spec.map φ ≫ a = b}
variable {X X' : AlgebraicSpace S} {g' : X' ⟶ X}
variable {f' : X' ⟶ ofOver (Over.mk b)}
variable {f : X ⟶ ofOver (Over.mk a)}

/-- Direct-image section evaluation and its inverse respect the coefficient actions
of a commutative affine-base square. -/
theorem sectionComparison_laws (sq : CommSq g' f' f (ofOverHomMk (Spec.map φ) w)) :
    let ΓX := moduleGlobalSectionsFunctor X ⋙
      ModuleCat.restrictScalars (Hom.affineGlobalSectionsMap f).hom
    let ΓX' := (moduleGlobalSectionsFunctor X' ⋙
      ModuleCat.restrictScalars (Hom.affineGlobalSectionsMap f').hom) ⋙
        ModuleCat.restrictScalars φ.hom
    let e := gammaPushforwardIso g'
    let forward : ∀ F : X'.Modules, ΓX.obj ((pushforward g').obj F) → ΓX'.obj F :=
      fun F x ↦ e.hom.app F x
    let reverse : ∀ F : X'.Modules, ΓX'.obj F → ΓX.obj ((pushforward g').obj F) :=
      fun F x ↦ e.inv.app F x
    (∀ (F : X'.Modules) (r : A) (x : ΓX.obj ((pushforward g').obj F)),
      forward F (r • x) = r • forward F x) ∧
    (∀ (F : X'.Modules) (r : A) (x : ΓX'.obj F),
      reverse F (r • x) = r • reverse F x) := sorry

/-- Global sections of a direct image identify with global sections on the source,
with scalar restriction along the affine coefficient homomorphism. -/
def sectionComparison (sq : CommSq g' f' f (ofOverHomMk (Spec.map φ) w)) :
    pushforward g' ⋙
        (moduleGlobalSectionsFunctor X ⋙
          ModuleCat.restrictScalars (Hom.affineGlobalSectionsMap f).hom) ≅
      (moduleGlobalSectionsFunctor X' ⋙
          ModuleCat.restrictScalars (Hom.affineGlobalSectionsMap f').hom) ⋙
        ModuleCat.restrictScalars φ.hom :=
  NatIso.ofComponents
    (fun F ↦
      { hom := ModuleCat.ofHom
          (X := (underived f).obj ((pushforward g').obj F))
          (Y := (underived f' ⋙ ModuleCat.restrictScalars φ.hom).obj F)
          { toFun := (gammaPushforwardIso g').hom.app F
            map_add' := ((gammaPushforwardIso g').hom.app F).hom.map_add
            map_smul' := (sectionComparison_laws sq).1 F }
        inv := ModuleCat.ofHom
          (X := (underived f' ⋙ ModuleCat.restrictScalars φ.hom).obj F)
          (Y := (underived f).obj ((pushforward g').obj F))
          { toFun := (gammaPushforwardIso g').inv.app F
            map_add' := ((gammaPushforwardIso g').inv.app F).hom.map_add
            map_smul' := (sectionComparison_laws sq).2 F }
        hom_inv_id := ModuleCat.hom_ext (LinearMap.ext (fun x ↦
          ConcreteCategory.congr_hom
            ((gammaPushforwardIso g').hom_inv_id_app F) x))
        inv_hom_id := ModuleCat.hom_ext (LinearMap.ext (fun x ↦
          ConcreteCategory.congr_hom
            ((gammaPushforwardIso g').inv_hom_id_app F) x)) })
    (fun a ↦ ModuleCat.hom_ext (LinearMap.ext (fun x ↦
      ConcreteCategory.congr_hom
        ((gammaPushforwardIso g').hom.naturality a) x)))

/-- Global sections takes the injective-model augmentation of a direct image of an
injective model to a quasi-isomorphism. -/
theorem derivedComparison_laws (sq : CommSq g' f' f (ofOverHomMk (Spec.map φ) w)) :
    ∀ K : CochainComplex X'.Modules ℤ,
      QuasiIso (((moduleGlobalSectionsFunctor X ⋙
        ModuleCat.restrictScalars (Hom.affineGlobalSectionsMap f).hom).mapHomologicalComplex
          (up ℤ)).map
        ((CochainComplex.KInjectiveResolution.Construction.augmentation.{u} X.Modules).app
          (((pushforward g').mapHomologicalComplex (up ℤ)).obj
            ((CochainComplex.KInjectiveResolution.Construction.replacement.{u}
              X'.Modules).obj K)))) := sorry

/-- The section comparison is evaluated on the same specified source injective model. -/
private def sectionModelIso (sq : CommSq g' f' f (ofOverHomMk (Spec.map φ) w)) :
    KInjectiveModel.derived.{u} (pushforward g' ⋙ underived f) ≅
      KInjectiveModel.derived.{u} (underived f' ⋙ ModuleCat.restrictScalars φ.hom) :=
  Localization.liftNatIso (DerivedCategory.Q (C := X'.Modules))
    (HomologicalComplex.quasiIso X'.Modules (up ℤ))
    (DerivedCategory.Q ⋙ KInjectiveModel.derived.{u} (pushforward g' ⋙ underived f))
    (DerivedCategory.Q ⋙ KInjectiveModel.derived.{u}
      (underived f' ⋙ ModuleCat.restrictScalars φ.hom))
    (KInjectiveModel.derived.{u} (pushforward g' ⋙ underived f))
    (KInjectiveModel.derived.{u} (underived f' ⋙ ModuleCat.restrictScalars φ.hom))
    (KInjectiveModel.fac.{u} (pushforward g' ⋙ underived f) ≪≫
      isoWhiskerLeft (CochainComplex.KInjectiveResolution.Construction.replacement.{u} X'.Modules)
        (isoWhiskerRight (NatIso.mapHomologicalComplex (sectionComparison sq) (up ℤ))
          DerivedCategory.Q) ≪≫
      (KInjectiveModel.fac.{u} (underived f' ⋙ ModuleCat.restrictScalars φ.hom)).symm)

/-- Scalar-valued derived global sections of a derived direct image are the
scalar restriction of derived global sections on the source. -/
def pushforwardIso (sq : CommSq g' f' f (ofOverHomMk (Spec.map φ) w)) :
    moduleDerivedPushforward g' ⋙ functor f ≅
      functor f' ⋙ ModuleCat.derivedRestrictionOfScalars φ.hom :=
  isoWhiskerLeft (moduleDerivedPushforward g') (modelIso f) ≪≫
    isoWhiskerRight
      (@KInjectiveModel.isoOfModel.{u} _ _ _ _ _ _ _ _ _ (pushforward g') _
        (moduleDerivedPushforward g') (moduleDerivedPushforward.unit g')
        (moduleDerivedPushforward.isRightDerived g')).symm
      (KInjectiveModel.derived.{u} (underived f)) ≪≫
    (KInjectiveModel.compositionIso (pushforward g') (underived f)
      (derivedComparison_laws sq)).symm ≪≫
    sectionModelIso sq ≪≫
    (KInjectiveModel.postcomposeIso (underived f') (ModuleCat.restrictScalars φ.hom)).symm ≪≫
    isoWhiskerRight (modelIso f').symm (ModuleCat.derivedRestrictionOfScalars φ.hom)

/-- Scalar base change of derived global sections is the scalar-adjunction transpose
of global sections of the geometric unit and the direct-image comparison. -/
def pullbackMap (sq : CommSq g' f' f (ofOverHomMk (Spec.map φ) w)) (K : ModuleDerived X) :
    (ModuleCat.derivedExtensionOfScalars φ.hom).obj ((functor f).obj K) ⟶
      (functor f').obj ((ModuleDerived.pullback g').obj K) :=
  ((ModuleCat.derivedExtensionRestrictionAdjunction φ.hom).homEquiv _ _).symm
    ((functor f).map ((AlgebraicSpace.derivedPullbackPushforwardAdjunction g').unit.app K) ≫
      (pushforwardIso sq).hom.app ((ModuleDerived.pullback g').obj K))

/-- Scalar base change commutes with the geometric counit and the scalar counit. -/
theorem pullbackMap_counit (sq : CommSq g' f' f (ofOverHomMk (Spec.map φ) w))
    (L : ModuleDerived X') :
    pullbackMap sq ((moduleDerivedPushforward g').obj L) ≫
        (functor f').map ((AlgebraicSpace.derivedPullbackPushforwardAdjunction g').counit.app L) =
      (ModuleCat.derivedExtensionOfScalars φ.hom).map ((pushforwardIso sq).hom.app L) ≫
        (ModuleCat.derivedExtensionRestrictionAdjunction φ.hom).counit.app ((functor f').obj L) :=
  sorry

end Comparison

end AlgebraicGeometry.AlgebraicSpace.Modules.AffineGlobalSections
