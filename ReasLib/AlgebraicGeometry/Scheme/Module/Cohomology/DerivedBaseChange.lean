/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension
public import ReasLib.AlgebraicGeometry.Scheme.BaseChange.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.ChangeOfRings.Pullback
public import ReasLib.CategoryTheory.Adjunction.BaseChange
public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy
public import ReasLib.CategoryTheory.Functor.Derived.Adjunction.Restriction

/-!
# Derived base change for module cohomology

This file defines derived global sections over an affine base, the corresponding object after
affine base change, and the canonical comparison morphism between them.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Affine tilde sheafification followed by pullback to a scheme over the affine base. -/
abbrev affineBaseModuleAssociatedFunctor
    (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) : ModuleCat A ⥤ X.Modules :=
  tilde.functor (CommRingCat.of A) ⋙ Scheme.Modules.pullback f

/-- Pushforward to an affine base followed by global sections. -/
abbrev affineBaseModuleGlobalSectionsFunctor
    (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) : X.Modules ⥤ ModuleCat A :=
  Scheme.Modules.pushforward f ⋙
    (moduleSpecΓFunctor (R := CommRingCat.of A) :
      (Spec (CommRingCat.of A)).Modules ⥤ ModuleCat A)

/-- Affine associated-module formation is additive. -/
noncomputable instance affineBaseModuleAssociatedFunctorAdditive
    (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) :
    (affineBaseModuleAssociatedFunctor A f).Additive :=
  let hTilde :=
    AlgebraicGeometry.instAdditiveModuleCatCarrierModulesSpecOfFunctor (R := CommRingCat.of A)
  let hPullback : (Scheme.Modules.pullback f).Additive := inferInstance
  { map_add := by
      intro M N g h
      change
        (Scheme.Modules.pullback f).map
            ((tilde.functor (CommRingCat.of A)).map (g + h)) =
          (Scheme.Modules.pullback f).map
              ((tilde.functor (CommRingCat.of A)).map g) +
            (Scheme.Modules.pullback f).map
              ((tilde.functor (CommRingCat.of A)).map h)
      rw [hTilde.map_add (f := g) (g := h),
        hPullback.map_add
          (f := (tilde.functor (CommRingCat.of A)).map g)
          (g := (tilde.functor (CommRingCat.of A)).map h)] }

/-- Affine-base global sections are additive. -/
noncomputable instance affineBaseModuleGlobalSectionsFunctorAdditive
    (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) :
    (affineBaseModuleGlobalSectionsFunctor A f).Additive :=
  let hPushforward : (Scheme.Modules.pushforward f).Additive := inferInstance
  let hSections : (moduleSpecΓFunctor (R := CommRingCat.of A)).Additive :=
    @Adjunction.right_adjoint_additive _ _ _ _ _ _ _ _
      (tilde.adjunction (R := CommRingCat.of A))
      (AlgebraicGeometry.instAdditiveModuleCatCarrierModulesSpecOfFunctor (R := CommRingCat.of A))
  { map_add := by
      intro M N g h
      change
        (moduleSpecΓFunctor (R := CommRingCat.of A)).map
            ((Scheme.Modules.pushforward f).map (g + h)) =
          (moduleSpecΓFunctor (R := CommRingCat.of A)).map
              ((Scheme.Modules.pushforward f).map g) +
            (moduleSpecΓFunctor (R := CommRingCat.of A)).map
              ((Scheme.Modules.pushforward f).map h)
      rw [hPushforward.map_add (f := g) (g := h),
        hSections.map_add
          (f := (Scheme.Modules.pushforward f).map g)
          (g := (Scheme.Modules.pushforward f).map h)] }

/-- Affine associated modules and affine-base global sections form the composite tilde-pullback
adjunction. -/
noncomputable def affineBaseModuleAdjunction
    (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) :
    affineBaseModuleAssociatedFunctor A f ⊣ affineBaseModuleGlobalSectionsFunctor A f :=
  (tilde.adjunction (R := CommRingCat.of A)).comp
    (Scheme.Modules.pullbackPushforwardAdjunction f)

/-- The affine associated-module/global-sections adjunction applied degreewise to cochain
complexes. -/
noncomputable def affineBaseModuleComplexAdjunction
    (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) :
    (affineBaseModuleAssociatedFunctor A f).mapHomologicalComplex (up ℤ) ⊣
      (affineBaseModuleGlobalSectionsFunctor A f).mapHomologicalComplex (up ℤ) :=
  Adjunction.mapHomologicalComplexAdjunction (affineBaseModuleAdjunction A f) (up ℤ)

/-- The affine associated-module/global-sections adjunction transported to cochain homotopy
categories. -/
noncomputable def affineBaseModuleHomotopyAdjunction
    (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) :
    (affineBaseModuleAssociatedFunctor A f).mapHomotopyCategory (up ℤ) ⊣
      (affineBaseModuleGlobalSectionsFunctor A f).mapHomotopyCategory (up ℤ) :=
  Adjunction.mapHomotopyCategoryAdjunction (affineBaseModuleAdjunction A f)

namespace AffineBaseModuleDerivedAdjunction

/-- The affine associated-module functor admits its standard total left derived functor. -/
abbrev HasLeftDerived
    (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) : Prop :=
  (@Functor.Homotopy.toDerived
    (ModuleCat A) inferInstance inferInstance
    X.Modules inferInstance inferInstance (HasDerivedCategory.standard X.Modules)
    (affineBaseModuleAssociatedFunctor A f)
    (affineBaseModuleAssociatedFunctorAdditive A f)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (ModuleCat A) (up ℤ))

/-- Affine-base global sections have their standard total right derived functor. -/
abbrev HasRightDerived
    (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) : Prop :=
  (@Functor.Homotopy.toDerived
    X.Modules inferInstance inferInstance
    (ModuleCat A) inferInstance inferInstance inferInstance
    (affineBaseModuleGlobalSectionsFunctor A f)
    (affineBaseModuleGlobalSectionsFunctorAdditive A f)).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso X.Modules (up ℤ))

/-- The two absolute-derived conditions needed for the affine derived adjunction. -/
abbrev HasPair
    (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A))
    [hLeft : (Functor.Homotopy.toDerived
      (affineBaseModuleAssociatedFunctor A f)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (ModuleCat A) (up ℤ))]
    [hRight : (Functor.Homotopy.toDerived
      (affineBaseModuleGlobalSectionsFunctor A f)).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso X.Modules (up ℤ))] : Prop :=
  @CategoryTheory.Adjunction.TotalDerived.HasPair
    (HomotopyCategory (ModuleCat A) (up ℤ))
    (HomotopyCategory X.Modules (up ℤ))
    (DerivedCategory (ModuleCat A)) (DerivedCategory X.Modules)
    inferInstance inferInstance inferInstance inferInstance
    ((affineBaseModuleAssociatedFunctor A f).mapHomotopyCategory (up ℤ))
    ((affineBaseModuleGlobalSectionsFunctor A f).mapHomotopyCategory (up ℤ))
    (HomotopyCategory.quasiIso (ModuleCat A) (up ℤ))
    (HomotopyCategory.quasiIso X.Modules (up ℤ))
    DerivedCategory.Qh DerivedCategory.Qh inferInstance inferInstance hLeft hRight

end AffineBaseModuleDerivedAdjunction

/-- The standard total left-derived affine associated-module functor. -/
abbrev affineBaseModuleDerivedAssociatedFunctor
    (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A))
    [AffineBaseModuleDerivedAdjunction.HasLeftDerived A f] :
    DerivedCategory (ModuleCat A) ⥤ DerivedCategory X.Modules :=
  Functor.LeftDerived.Homotopy.functor (affineBaseModuleAssociatedFunctor A f)

/-- The standard total right-derived global-sections functor relative to an affine base. -/
abbrev affineBaseModuleDerivedGlobalSectionsFunctor
    (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A))
    [AffineBaseModuleDerivedAdjunction.HasRightDerived A f] :
    DerivedCategory X.Modules ⥤ DerivedCategory (ModuleCat A) :=
  Functor.RightDerived.Homotopy.functor (affineBaseModuleGlobalSectionsFunctor A f)

/-- The canonical adjunction between the standard affine derived functors. -/
noncomputable def affineBaseModuleDerivedAdjunction
    (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A))
    [hLeft : AffineBaseModuleDerivedAdjunction.HasLeftDerived A f]
    [hRight : AffineBaseModuleDerivedAdjunction.HasRightDerived A f]
    [hPair : AffineBaseModuleDerivedAdjunction.HasPair A f] :
    affineBaseModuleDerivedAssociatedFunctor A f ⊣
      affineBaseModuleDerivedGlobalSectionsFunctor A f :=
  @CategoryTheory.Adjunction.TotalDerived.HasPair.derived
    (HomotopyCategory (ModuleCat A) (up ℤ))
    (HomotopyCategory X.Modules (up ℤ))
    (DerivedCategory (ModuleCat A)) (DerivedCategory X.Modules)
    inferInstance inferInstance inferInstance inferInstance
    ((affineBaseModuleAssociatedFunctor A f).mapHomotopyCategory (up ℤ))
    ((affineBaseModuleGlobalSectionsFunctor A f).mapHomotopyCategory (up ℤ))
    (affineBaseModuleHomotopyAdjunction A f)
    (HomotopyCategory.quasiIso (ModuleCat A) (up ℤ))
    (HomotopyCategory.quasiIso X.Modules (up ℤ))
    DerivedCategory.Qh DerivedCategory.Qh inferInstance inferInstance hLeft hRight hPair

/-- The derived global-sections object of a module relative to an affine base. -/
abbrev affineBaseModuleDerivedGlobalSections
    (A : Type u) [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A))
    [AffineBaseModuleDerivedAdjunction.HasRightDerived A f]
    (ℱ : X.Modules) : DerivedCategory (ModuleCat A) :=
  (affineBaseModuleDerivedGlobalSectionsFunctor A f).obj
    ((DerivedCategory.singleFunctor X.Modules 0).obj ℱ)

/-- The derived global-sections object after affine base change. -/
abbrev affineBaseChangedModuleDerivedGlobalSections
    (A A' : Type u) [CommRing A] [CommRing A'] [Algebra A A']
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    [AffineBaseModuleDerivedAdjunction.HasRightDerived A'
      (Scheme.AffineBaseChange.toBase A A' f)]
    (ℱ : X.Modules) : DerivedCategory (ModuleCat A') :=
  affineBaseModuleDerivedGlobalSections A'
    (Scheme.AffineBaseChange.toBase A A' f)
    (Scheme.Modules.AffineBaseChange.baseChange A A' f ℱ)

namespace AffineBaseChangeDerivedCompatibility

/-- Derived scalar extension exists for the selected map of affine bases. -/
abbrev HasScalarExtension
    (A A' : Type u) [CommRing A] [CommRing A'] [Algebra A A'] : Prop :=
  (ModuleCat.extendScalarsToDerived.{u, u, u}
    (algebraMap A A')).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso (ModuleCat.{u} A) (up ℤ))

/-- Pullback along the projection from an affine base change admits its total left derived
functor. -/
abbrev HasPullback
    (A A' : Type u) [CommRing A] [CommRing A'] [Algebra A A']
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) : Prop :=
  (@Functor.Homotopy.toDerived
    X.Modules inferInstance inferInstance
    (Scheme.AffineBaseChange.baseChange A A' f).Modules inferInstance inferInstance
      (HasDerivedCategory.standard
        (Scheme.AffineBaseChange.baseChange A A' f).Modules)
    (Scheme.Modules.pullback (Scheme.AffineBaseChange.toSource A A' f))
    inferInstance).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso X.Modules (up ℤ))

/-- The scalar-extension-first iterated functor has the universal property of the derived
composite. -/
abbrev SourceRoute
    (A A' : Type u) [CommRing A] [CommRing A'] [Algebra A A']
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    [HasScalarExtension A A']
    [AffineBaseModuleDerivedAdjunction.HasLeftDerived A'
      (Scheme.AffineBaseChange.toBase A A' f)] : Prop :=
  (ModuleCat.derivedExtensionOfScalars (algebraMap A A') ⋙
      affineBaseModuleDerivedAssociatedFunctor A'
        (Scheme.AffineBaseChange.toBase A A' f)).IsLeftDerivedFunctor
    (Functor.LeftDerived.Homotopy.Composition.counit
      (affineBaseModuleAssociatedFunctor A'
        (Scheme.AffineBaseChange.toBase A A' f))
      (ModuleCat.extendScalars (algebraMap A A')))
    (HomotopyCategory.quasiIso (ModuleCat A) (up ℤ))

/-- The associated-module-first iterated functor has the universal property of the derived
composite. -/
abbrev TargetRoute
    (A A' : Type u) [CommRing A] [CommRing A'] [Algebra A A']
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    [AffineBaseModuleDerivedAdjunction.HasLeftDerived A f]
    [HasPullback A A' f] : Prop :=
  (affineBaseModuleDerivedAssociatedFunctor A f ⋙
      Functor.LeftDerived.Homotopy.functor
        (Scheme.Modules.pullback
          (Scheme.AffineBaseChange.toSource A A' f))).IsLeftDerivedFunctor
    (Functor.LeftDerived.Homotopy.Composition.counit
      (Scheme.Modules.pullback (Scheme.AffineBaseChange.toSource A A' f))
      (affineBaseModuleAssociatedFunctor A f))
    (HomotopyCategory.quasiIso (ModuleCat A) (up ℤ))

end AffineBaseChangeDerivedCompatibility

/-- The standard total left-derived pullback along the projection from an affine base change. -/
abbrev affineBaseChangeModuleDerivedPullbackFunctor
    (A A' : Type u) [CommRing A] [CommRing A'] [Algebra A A']
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    [AffineBaseChangeDerivedCompatibility.HasPullback A A' f] :
    DerivedCategory X.Modules ⥤
      DerivedCategory (Scheme.AffineBaseChange.baseChange A A' f).Modules :=
  Functor.LeftDerived.Homotopy.functor
    (Scheme.Modules.pullback (Scheme.AffineBaseChange.toSource A A' f))

/-- Extension of scalars followed by affine associated-module formation is canonically the same
as affine associated-module formation followed by pullback to the changed base. -/
noncomputable def affineBaseModulePullbackSquare
    (A A' : Type u) [CommRing A] [CommRing A'] [Algebra A A']
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) :
    ModuleCat.extendScalars (algebraMap A A') ⋙
        affineBaseModuleAssociatedFunctor A'
          (Scheme.AffineBaseChange.toBase A A' f) ≅
      affineBaseModuleAssociatedFunctor A f ⋙
        Scheme.Modules.pullback (Scheme.AffineBaseChange.toSource A A' f) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (tilde.ChangeOfRings.Pullback.iso
        (CommRingCat.ofHom (algebraMap A A'))).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (Scheme.Modules.pullbackComp
        (Scheme.AffineBaseChange.toBase A A' f)
        (Scheme.AffineBaseChange.specMap A A')) ≪≫
    Functor.isoWhiskerLeft _
      (Scheme.Modules.pullbackCongr
        (Limits.pullback.condition (f := f)
          (g := Scheme.AffineBaseChange.specMap A A')).symm) ≪≫
    Functor.isoWhiskerLeft _
      (Scheme.Modules.pullbackComp
        (Scheme.AffineBaseChange.toSource A A' f) f).symm ≪≫
    (Functor.associator _ _ _).symm

/-- The two canonical iterated total-left-derived routes form the derived affine pullback
square. -/
noncomputable def affineBaseModuleDerivedPullbackSquare
    (A A' : Type u) [CommRing A] [CommRing A'] [Algebra A A']
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    [AffineBaseModuleDerivedAdjunction.HasLeftDerived A f]
    [AffineBaseModuleDerivedAdjunction.HasLeftDerived A'
      (Scheme.AffineBaseChange.toBase A A' f)]
    [AffineBaseChangeDerivedCompatibility.HasScalarExtension A A']
    [AffineBaseChangeDerivedCompatibility.HasPullback A A' f]
    [AffineBaseChangeDerivedCompatibility.SourceRoute A A' f]
    [AffineBaseChangeDerivedCompatibility.TargetRoute A A' f] :
    ModuleCat.derivedExtensionOfScalars (algebraMap A A') ⋙
        affineBaseModuleDerivedAssociatedFunctor A'
          (Scheme.AffineBaseChange.toBase A A' f) ≅
      affineBaseModuleDerivedAssociatedFunctor A f ⋙
        affineBaseChangeModuleDerivedPullbackFunctor A A' f :=
  Functor.leftDerivedNatIso
    (ModuleCat.derivedExtensionOfScalars (algebraMap A A') ⋙
      affineBaseModuleDerivedAssociatedFunctor A'
        (Scheme.AffineBaseChange.toBase A A' f))
    (affineBaseModuleDerivedAssociatedFunctor A f ⋙
      affineBaseChangeModuleDerivedPullbackFunctor A A' f)
    (Functor.LeftDerived.Homotopy.Composition.counit
      (affineBaseModuleAssociatedFunctor A'
        (Scheme.AffineBaseChange.toBase A A' f))
      (ModuleCat.extendScalars (algebraMap A A')))
    (Functor.LeftDerived.Homotopy.Composition.counit
      (Scheme.Modules.pullback (Scheme.AffineBaseChange.toSource A A' f))
      (affineBaseModuleAssociatedFunctor A f))
    (HomotopyCategory.quasiIso (ModuleCat A) (up ℤ))
    ((Functor.LeftDerived.Homotopy.Composition.toDerivedIso
      (affineBaseModuleAssociatedFunctor A'
        (Scheme.AffineBaseChange.toBase A A' f))
      (ModuleCat.extendScalars (algebraMap A A'))
      (ModuleCat.extendScalars (algebraMap A A') ⋙
        affineBaseModuleAssociatedFunctor A'
          (Scheme.AffineBaseChange.toBase A A' f))
      (Iso.refl _)).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryIso (affineBaseModulePullbackSquare A A' f))
      (DerivedCategory.Qh :
        HomotopyCategory (Scheme.AffineBaseChange.baseChange A A' f).Modules (up ℤ) ⥤
          DerivedCategory (Scheme.AffineBaseChange.baseChange A A' f).Modules) ≪≫
    Functor.LeftDerived.Homotopy.Composition.toDerivedIso
      (Scheme.Modules.pullback (Scheme.AffineBaseChange.toSource A A' f))
      (affineBaseModuleAssociatedFunctor A f)
      (affineBaseModuleAssociatedFunctor A f ⋙
        Scheme.Modules.pullback (Scheme.AffineBaseChange.toSource A A' f))
      (Iso.refl _))

/-- The canonical derived affine base-change map, obtained as the right mate of the derived
pullback square and evaluated on a module in degree zero. -/
noncomputable def affineBaseModuleDerivedGlobalSectionsBaseChangeMap
    (A A' : Type u) [CommRing A] [CommRing A'] [Algebra A A']
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    [AffineBaseModuleDerivedAdjunction.HasLeftDerived A f]
    [AffineBaseModuleDerivedAdjunction.HasRightDerived A f]
    [AffineBaseModuleDerivedAdjunction.HasPair A f]
    [AffineBaseModuleDerivedAdjunction.HasLeftDerived A'
      (Scheme.AffineBaseChange.toBase A A' f)]
    [AffineBaseModuleDerivedAdjunction.HasRightDerived A'
      (Scheme.AffineBaseChange.toBase A A' f)]
    [AffineBaseModuleDerivedAdjunction.HasPair A'
      (Scheme.AffineBaseChange.toBase A A' f)]
    [AffineBaseChangeDerivedCompatibility.HasScalarExtension A A']
    [AffineBaseChangeDerivedCompatibility.HasPullback A A' f]
    [AffineBaseChangeDerivedCompatibility.SourceRoute A A' f]
    [AffineBaseChangeDerivedCompatibility.TargetRoute A A' f]
    (ℱ : X.Modules) :
    (ModuleCat.derivedExtensionOfScalars (algebraMap A A')).obj
        (affineBaseModuleDerivedGlobalSections A f ℱ) ⟶
      affineBaseChangedModuleDerivedGlobalSections A A' f ℱ := by
  let K := (HomotopyCategory.singleFunctor X.Modules 0).obj ℱ
  let mate := CategoryTheory.DerivedBaseChange.app
    (affineBaseModuleDerivedAdjunction A f)
    (affineBaseModuleDerivedAdjunction A'
      (Scheme.AffineBaseChange.toBase A A' f))
    (affineBaseModuleDerivedPullbackSquare A A' f)
    ((DerivedCategory.Qh : HomotopyCategory X.Modules (up ℤ) ⥤
      DerivedCategory X.Modules).obj K)
  let singleIso :
      (Functor.Homotopy.toDerived
        (Scheme.Modules.pullback
          (Scheme.AffineBaseChange.toSource A A' f))).obj K ≅
        (DerivedCategory.singleFunctor
          (Scheme.AffineBaseChange.baseChange A A' f).Modules 0).obj
            (Scheme.Modules.AffineBaseChange.baseChange A A' f ℱ) :=
    (DerivedCategory.Qh :
      HomotopyCategory (Scheme.AffineBaseChange.baseChange A A' f).Modules (up ℤ) ⥤
        DerivedCategory (Scheme.AffineBaseChange.baseChange A A' f).Modules).mapIso
      ((HomotopyCategory.quotient
        (Scheme.AffineBaseChange.baseChange A A' f).Modules (up ℤ)).mapIso
          ((HomologicalComplex.singleMapHomologicalComplex
            (Scheme.Modules.pullback (Scheme.AffineBaseChange.toSource A A' f))
            (up ℤ) 0).app ℱ))
  let comparison :=
    (affineBaseModuleDerivedGlobalSectionsFunctor A'
      (Scheme.AffineBaseChange.toBase A A' f)).map
      ((Functor.LeftDerived.Homotopy.counit
        (Scheme.Modules.pullback
          (Scheme.AffineBaseChange.toSource A A' f))).app K ≫ singleIso.hom)
  exact mate ≫ comparison

end AlgebraicGeometry.Scheme.Modules
