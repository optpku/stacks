/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.ChangeOfRings.Pullback
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived.Composition

/-!
# Ambient Affine Derived Pullback

This module compares derived extension of scalars with derived pullback of module sheaves on
affine schemes, after including complexes with quasicoherent cohomology into the ambient derived
category.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- The affine equivalence from modules to quasi-coherent modules in the ringed-space
presentation. -/
noncomputable abbrev affineModuleEquivalence (A : CommRingCat.{u}) :
    ModuleCat A ≌ RingedSpace.QCoh (Spec A).toRingedSpace :=
  AlgebraicGeometry.tildeEquiv.trans (Scheme.QCoh.ringedSpaceEquivalence (Spec A))

/-- The exact affine associated-module functor, including quasi-coherent modules into all
ringed-space modules. -/
noncomputable abbrev affineModuleExact (A : CommRingCat.{u})
    [HasDerivedCategory.{u + 1} (RingedSpace.QCoh (Spec A).toRingedSpace)] :
    ModuleCat A ⥤ₑ (Spec A).toRingedSpace.Modules :=
  (Equivalence.MapDerivedCategory.forwardExact (affineModuleEquivalence A)).comp
    (ExactFunctor.of
      (RingedSpace.quasiCoherentModuleProperty (Spec A).toRingedSpace).ι)

/-- The affine functor from module-derived categories to derived modules with
quasi-coherent cohomology. -/
noncomputable abbrev affineFunctor (A : CommRingCat.{u})
    [HasDerivedCategory.{u + 1} (RingedSpace.QCoh (Spec A).toRingedSpace)] :
    DerivedCategory (ModuleCat A) ⥤
      DerivedCategory.CohomologyIn
        (RingedSpace.quasiCoherentModuleProperty (Spec A).toRingedSpace) :=
  (affineModuleEquivalence A).mapDerivedCategory.functor ⋙
    DerivedCategory.CohomologyIn.Comparison.functor
      (RingedSpace.quasiCoherentModuleProperty (Spec A).toRingedSpace)

/-- The exact affine module functor is the usual tilde functor followed by the
identity-on-data change to the ringed-space presentation. -/
noncomputable def affineModuleFunctorIso (A : CommRingCat.{u})
    [HasDerivedCategory.{u + 1} (RingedSpace.QCoh (Spec A).toRingedSpace)] :
    (affineModuleExact A).obj ≅
      AlgebraicGeometry.tilde.functor A ⋙ Scheme.Modules.toRingedSpace (Spec A) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Scheme.QCoh.ringedSpaceEquivalence.inclusionIso (Spec A)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Iso.refl (AlgebraicGeometry.tilde.functor A)) _

/-- Forgetting the quasi-coherent target identifies the affine derived functor with the
derived functor of the exact affine module functor. -/
noncomputable def affineFunctor.inclusionIso (A : CommRingCat.{u})
    [HasDerivedCategory.{u + 1} (RingedSpace.QCoh (Spec A).toRingedSpace)] :
    affineFunctor A ⋙
        (DerivedCategory.cohomologyIn
          (RingedSpace.quasiCoherentModuleProperty (Spec A).toRingedSpace)).ι ≅
      (affineModuleExact A).mapDerivedCategory :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (DerivedCategory.CohomologyIn.Comparison.compιIso
        (RingedSpace.quasiCoherentModuleProperty (Spec A).toRingedSpace)) ≪≫
    (ExactFunctor.MapDerivedCategory.compFunctorIso
      (Equivalence.MapDerivedCategory.forwardExact (affineModuleEquivalence A))
      (ExactFunctor.of
        (RingedSpace.quasiCoherentModuleProperty (Spec A).toRingedSpace).ι)).symm

/-- Scheme-module pullback agrees with ringed-space module pullback under the
identity-on-data presentation equivalences. -/
noncomputable def modulePullbackToRingedSpaceIso {X Y : Scheme.{u}} (f : Y ⟶ X) :
    Scheme.Modules.pullback f ⋙ Scheme.Modules.toRingedSpace Y ≅
      Scheme.Modules.toRingedSpace X ⋙ RingedSpace.Hom.pullback f.toLRSHom.toShHom :=
  Iso.refl _

/-- The affine change-of-rings comparison, expressed in the ringed-space module
presentation used by derived quasi-coherent pullback. -/
noncomputable def affineModulePullbackIso {A B : CommRingCat.{u}} (φ : A ⟶ B)
    [HasDerivedCategory.{u + 1} (RingedSpace.QCoh (Spec A).toRingedSpace)]
    [HasDerivedCategory.{u + 1} (RingedSpace.QCoh (Spec B).toRingedSpace)] :
    ModuleCat.extendScalars φ.hom ⋙ (affineModuleExact B).obj ≅
      (affineModuleExact A).obj ⋙
        RingedSpace.Hom.pullback (Spec.map φ).toLRSHom.toShHom :=
  Functor.isoWhiskerLeft (ModuleCat.extendScalars φ.hom) (affineModuleFunctorIso B) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (AlgebraicGeometry.tilde.ChangeOfRings.Pullback.iso φ).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (modulePullbackToRingedSpaceIso (Spec.map φ)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (affineModuleFunctorIso A).symm _

/-- The canonical localization counit for the affine functor after forgetting
quasi-coherent cohomology. -/
noncomputable def affineFunctor.inclusionCounit (A : CommRingCat.{u})
    [HasDerivedCategory.{u + 1} (RingedSpace.QCoh (Spec A).toRingedSpace)] :
    (DerivedCategory.Qh : HomotopyCategory (ModuleCat A) (up ℤ) ⥤
        DerivedCategory (ModuleCat A)) ⋙
        (affineFunctor A ⋙
          (DerivedCategory.cohomologyIn
            (RingedSpace.quasiCoherentModuleProperty (Spec A).toRingedSpace)).ι) ⟶
      Functor.Homotopy.toDerived (affineModuleExact A).obj :=
  Functor.whiskerLeft DerivedCategory.Qh (affineFunctor.inclusionIso A).hom ≫
    (affineModuleExact A).obj.mapDerivedCategoryFactorsh.hom

/-- The affine functor followed by ambient inclusion is the left-derived functor of the
exact affine associated-module functor. -/
instance affineFunctor.inclusionIsLeftDerived (A : CommRingCat.{u})
    [HasDerivedCategory.{u + 1} (RingedSpace.QCoh (Spec A).toRingedSpace)] :
    (affineFunctor A ⋙
      (DerivedCategory.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty (Spec A).toRingedSpace)).ι).IsLeftDerivedFunctor
      (affineFunctor.inclusionCounit A)
      (HomotopyCategory.quasiIso (ModuleCat A) (up ℤ)) := sorry

/-- The canonical counit for the route given by derived scalar extension followed by the
affine functor and ambient inclusion. -/
noncomputable def affineExtensionRouteCounit {A B : CommRingCat.{u}} (φ : A ⟶ B)
    [HasDerivedCategory.{u + 1} (RingedSpace.QCoh (Spec B).toRingedSpace)] :
    (DerivedCategory.Qh : HomotopyCategory (ModuleCat A) (up ℤ) ⥤
        DerivedCategory (ModuleCat A)) ⋙
        (ModuleCat.derivedExtensionOfScalars φ.hom ⋙
          (affineFunctor B ⋙
            (DerivedCategory.cohomologyIn
              (RingedSpace.quasiCoherentModuleProperty (Spec B).toRingedSpace)).ι)) ⟶
      (ModuleCat.extendScalars φ.hom).mapHomotopyCategory (up ℤ) ⋙
        Functor.Homotopy.toDerived (affineModuleExact B).obj :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (ModuleCat.derivedExtensionOfScalarsCounit φ.hom) _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (affineFunctor.inclusionCounit B)

/-- The scalar-extension-first affine route has the universal property of the derived
composite. -/
instance affineExtensionRouteIsLeftDerived {A B : CommRingCat.{u}} (φ : A ⟶ B)
    [HasDerivedCategory.{u + 1} (RingedSpace.QCoh (Spec B).toRingedSpace)] :
    (ModuleCat.derivedExtensionOfScalars φ.hom ⋙
      (affineFunctor B ⋙
        (DerivedCategory.cohomologyIn
          (RingedSpace.quasiCoherentModuleProperty (Spec B).toRingedSpace)).ι)).IsLeftDerivedFunctor
        (affineExtensionRouteCounit φ)
        (HomotopyCategory.quasiIso (ModuleCat A) (up ℤ)) := sorry

/-- The canonical localization counit for derived module pullback on a scheme. -/
noncomputable def modulePullbackDerivedCounit {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (DerivedCategory.Qh : HomotopyCategory X.toRingedSpace.Modules (up ℤ) ⥤
        DerivedCategory X.toRingedSpace.Modules) ⋙
        RingedSpace.modulePullbackDerived f.toLRSHom.toShHom ⟶
      RingedSpace.modulePullbackToDerived f.toLRSHom.toShHom :=
  (RingedSpace.modulePullbackToDerived f.toLRSHom.toShHom).totalLeftDerivedCounit
    DerivedCategory.Qh (RingedSpace.ModuleQis X.toRingedSpace)

/-- The canonical counit for the route given by the affine functor followed by derived
module pullback. -/
noncomputable def affinePullbackRouteCounit {A B : CommRingCat.{u}} (φ : A ⟶ B)
    [HasDerivedCategory.{u + 1} (RingedSpace.QCoh (Spec A).toRingedSpace)] :
    (DerivedCategory.Qh : HomotopyCategory (ModuleCat A) (up ℤ) ⥤
        DerivedCategory (ModuleCat A)) ⋙
        ((affineFunctor A ⋙
          (DerivedCategory.cohomologyIn
            (RingedSpace.quasiCoherentModuleProperty (Spec A).toRingedSpace)).ι) ⋙
          RingedSpace.modulePullbackDerived (Spec.map φ).toLRSHom.toShHom) ⟶
      (affineModuleExact A).obj.mapHomotopyCategory (up ℤ) ⋙
        RingedSpace.modulePullbackToDerived (Spec.map φ).toLRSHom.toShHom :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (affineFunctor.inclusionCounit A) _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (modulePullbackDerivedCounit (Spec.map φ))

/-- The affine-associated-module-first pullback route has the universal property of the
derived composite. -/
instance affinePullbackRouteIsLeftDerived {A B : CommRingCat.{u}} (φ : A ⟶ B)
    [HasDerivedCategory.{u + 1} (RingedSpace.QCoh (Spec A).toRingedSpace)] :
    ((affineFunctor A ⋙
      (DerivedCategory.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty (Spec A).toRingedSpace)).ι) ⋙
      RingedSpace.modulePullbackDerived (Spec.map φ).toLRSHom.toShHom).IsLeftDerivedFunctor
        (affinePullbackRouteCounit φ)
        (HomotopyCategory.quasiIso (ModuleCat A) (up ℤ)) := sorry

/-- The affine change-of-rings square after forgetting quasi-coherent cohomology, obtained
canonically from uniqueness of left-derived functors. -/
noncomputable def affinePullbackAmbientIso {A B : CommRingCat.{u}} (φ : A ⟶ B)
    [HasDerivedCategory.{u + 1} (RingedSpace.QCoh (Spec A).toRingedSpace)]
    [HasDerivedCategory.{u + 1} (RingedSpace.QCoh (Spec B).toRingedSpace)] :
    ModuleCat.derivedExtensionOfScalars φ.hom ⋙
        (affineFunctor B ⋙
          (DerivedCategory.cohomologyIn
            (RingedSpace.quasiCoherentModuleProperty (Spec B).toRingedSpace)).ι) ≅
      (affineFunctor A ⋙
        (DerivedCategory.cohomologyIn
          (RingedSpace.quasiCoherentModuleProperty (Spec A).toRingedSpace)).ι) ⋙
        RingedSpace.modulePullbackDerived (Spec.map φ).toLRSHom.toShHom :=
  Functor.leftDerivedNatIso
    (ModuleCat.derivedExtensionOfScalars φ.hom ⋙
      (affineFunctor B ⋙
        (DerivedCategory.cohomologyIn
          (RingedSpace.quasiCoherentModuleProperty (Spec B).toRingedSpace)).ι))
    ((affineFunctor A ⋙
      (DerivedCategory.cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty (Spec A).toRingedSpace)).ι) ⋙
      RingedSpace.modulePullbackDerived (Spec.map φ).toLRSHom.toShHom)
    (affineExtensionRouteCounit φ) (affinePullbackRouteCounit φ)
    (HomotopyCategory.quasiIso (ModuleCat A) (up ℤ))
    ((Functor.LeftDerived.Homotopy.Composition.toDerivedIso
      (affineModuleExact B).obj (ModuleCat.extendScalars φ.hom)
      (ModuleCat.extendScalars φ.hom ⋙ (affineModuleExact B).obj)
      (Iso.refl _)).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryIso (affineModulePullbackIso φ))
      (DerivedCategory.Qh :
        HomotopyCategory (Spec B).toRingedSpace.Modules (up ℤ) ⥤
          DerivedCategory (Spec B).toRingedSpace.Modules) ≪≫
    Functor.LeftDerived.Homotopy.Composition.toDerivedIso
      (RingedSpace.Hom.pullback (Spec.map φ).toLRSHom.toShHom)
      (affineModuleExact A).obj
      ((affineModuleExact A).obj ⋙
        RingedSpace.Hom.pullback (Spec.map φ).toLRSHom.toShHom)
      (Iso.refl _))

end AlgebraicGeometry.Scheme.DerivedQCoh
