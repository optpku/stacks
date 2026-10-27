/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpensRingedSite

@[expose] public section

/-!
# Derived pullback-pushforward adjunctions on ringed spaces

The unit and counit use the specified cell and K-injective augmentations and the
ordinary cochain adjunction. Native localization descends these maps. The
absolute-derived pair is retained only as a compatibility input of the legacy
wrapper; it supplies no data to the construction.
-/

open AlgebraicGeometry CategoryTheory ComplexShape
open AlgebraicGeometry.RingedSpace.Hom
open scoped RingedSpace.Hom RingedSpaceDerivedPullback RingedSpaceDerivedPushforward

noncomputable section
universe u
namespace AlgebraicGeometry.RingedSpace

namespace DerivedAdjunction

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)

/-- The ordinary adjunction applied degreewise, with its actual unit and counit. -/
def cochainAdjunction :
    (pullback f).mapHomologicalComplex (up ℤ) ⊣
      (pushforward f).mapHomologicalComplex (up ℤ) :=
  Adjunction.mapHomologicalComplexAdjunction
    (RingedSpace.Hom.pullbackPushforwardAdjunction f) (up ℤ)

/-- Native uniqueness and localization compute public inverse image on the actual cell model. -/
def pullbackComputationIso (A : CochainComplex Y.Modules ℤ) :
    (L(f)^*).obj (DerivedCategory.Q.obj A) ≅
      DerivedCategory.Q.obj (((pullback f).mapHomologicalComplex (up ℤ)).obj
        (SheafOfModules.CellReplacement.model A)) :=
  (modulePullbackDerivedCellIso f).symm.app (DerivedCategory.Q.obj A) ≪≫
    (Functor.CellModel.fac (pullback f) (ModulePullbackCells.cochain_inverts f)).app A

/-- Native uniqueness compares public direct image with the actual K-injective producer. -/
def pushforwardModelIso :
    Functor.KInjectiveModel.derived (pushforward f) ≅ R(f)_* := by
  letI hNative : (moduleDerivedPushforward f).IsRightDerivedFunctor
      (moduleDerivedPushforward.unit f)
      (HomologicalComplex.quasiIso X.Modules (up ℤ)) :=
    Functor.RightDerived.KInjective.isRightDerived (pushforward f)
  exact @Functor.KInjectiveModel.isoOfModel
    X.Modules _ _ _ Y.Modules _ _ _ _ (pushforward f) _ (R(f)_*)
    (moduleDerivedPushforward.unit f) hNative

/-- Public direct image is computed by the specified K-injective replacement and localization. -/
def pushforwardComputationIso (B : CochainComplex X.Modules ℤ) :
    (R(f)_*).obj (DerivedCategory.Q.obj B) ≅
      DerivedCategory.Q.obj (((pushforward f).mapHomologicalComplex (up ℤ)).obj
        ((CochainComplex.KInjectiveResolution.Construction.replacement X.Modules).obj B)) :=
  (pushforwardModelIso f).symm.app (DerivedCategory.Q.obj B) ≪≫
    (Functor.KInjectiveModel.fac (pushforward f)).app B

/-- At a cochain input, reverse its cell augmentation, apply the ordinary unit,
then the direct image of the K-injective augmentation, and transport computations. -/
def unitOnCochain (A : CochainComplex Y.Modules ℤ) :
    DerivedCategory.Q.obj A ⟶ (L(f)^* ⋙ R(f)_*).obj (DerivedCategory.Q.obj A) :=
  (Functor.CellModel.inputAugmentationIso A).inv ≫
    DerivedCategory.Q.map ((cochainAdjunction f).unit.app
      (SheafOfModules.CellReplacement.model A)) ≫
    DerivedCategory.Q.map (((pushforward f).mapHomologicalComplex (up ℤ)).map
      ((CochainComplex.KInjectiveResolution.Construction.augmentation X.Modules).app
        (((pullback f).mapHomologicalComplex (up ℤ)).obj
          (SheafOfModules.CellReplacement.model A)))) ≫
    (pushforwardComputationIso f
      (((pullback f).mapHomologicalComplex (up ℤ)).obj
        (SheafOfModules.CellReplacement.model A))).inv ≫
    (R(f)_*).map (pullbackComputationIso f A).inv

/-- At a cochain input, compute direct then inverse image, apply inverse image
of the cell augmentation and the ordinary counit, then reverse the input's
K-injective augmentation. No inverse of a pulled-back augmentation is used. -/
def counitOnCochain (B : CochainComplex X.Modules ℤ) :
    (R(f)_* ⋙ L(f)^*).obj (DerivedCategory.Q.obj B) ⟶ DerivedCategory.Q.obj B :=
  (L(f)^*).map (pushforwardComputationIso f B).hom ≫
    (pullbackComputationIso f
      (((pushforward f).mapHomologicalComplex (up ℤ)).obj
        ((CochainComplex.KInjectiveResolution.Construction.replacement X.Modules).obj B))).hom ≫
    DerivedCategory.Q.map (((pullback f).mapHomologicalComplex (up ℤ)).map
      (SheafOfModules.CellReplacement.augmentation
        (((pushforward f).mapHomologicalComplex (up ℤ)).obj
          ((CochainComplex.KInjectiveResolution.Construction.replacement X.Modules).obj B)))) ≫
    DerivedCategory.Q.map ((cochainAdjunction f).counit.app
      ((CochainComplex.KInjectiveResolution.Construction.replacement X.Modules).obj B)) ≫
    (Functor.KInjectiveModel.inputAugmentationIso B).inv

/-- Naturality of the displayed unit in every original cochain map. -/
theorem unitOnCochain_naturality {A B : CochainComplex Y.Modules ℤ} (a : A ⟶ B) :
    DerivedCategory.Q.map a ≫ unitOnCochain f B =
      unitOnCochain f A ≫ (L(f)^* ⋙ R(f)_*).map (DerivedCategory.Q.map a) := sorry

/-- Naturality of the displayed counit in every original cochain map. -/
theorem counitOnCochain_naturality {A B : CochainComplex X.Modules ℤ} (a : A ⟶ B) :
    (R(f)_* ⋙ L(f)^*).map (DerivedCategory.Q.map a) ≫ counitOnCochain f B =
      counitOnCochain f A ≫ DerivedCategory.Q.map a := sorry

/-- The actual unit components before localization descent. -/
def unitOnCochains : DerivedCategory.Q ⋙ 𝟭 (DerivedCategory Y.Modules) ⟶
    DerivedCategory.Q ⋙ (L(f)^* ⋙ R(f)_*) where
  app A := unitOnCochain f A
  naturality := fun _ _ a ↦ unitOnCochain_naturality f a

/-- The actual counit components before localization descent. -/
def counitOnCochains : DerivedCategory.Q ⋙ (R(f)_* ⋙ L(f)^*) ⟶
    DerivedCategory.Q ⋙ 𝟭 (DerivedCategory X.Modules) where
  app B := counitOnCochain f B
  naturality := fun _ _ a ↦ counitOnCochain_naturality f a

/-- Native localization descends the specified unit maps. -/
def unit : 𝟭 (DerivedCategory Y.Modules) ⟶ L(f)^* ⋙ R(f)_* :=
  Localization.liftNatTrans (DerivedCategory.Q (C := Y.Modules))
    (HomologicalComplex.quasiIso Y.Modules (up ℤ))
    (DerivedCategory.Q ⋙ 𝟭 _) (DerivedCategory.Q ⋙ (L(f)^* ⋙ R(f)_*))
    (𝟭 _) (L(f)^* ⋙ R(f)_*) (unitOnCochains f)

/-- Native localization descends the specified counit maps. -/
def counit : R(f)_* ⋙ L(f)^* ⟶ 𝟭 (DerivedCategory X.Modules) :=
  Localization.liftNatTrans (DerivedCategory.Q (C := X.Modules))
    (HomologicalComplex.quasiIso X.Modules (up ℤ))
    (DerivedCategory.Q ⋙ (R(f)_* ⋙ L(f)^*)) (DerivedCategory.Q ⋙ 𝟭 _)
    (R(f)_* ⋙ L(f)^*) (𝟭 _) (counitOnCochains f)

/-- Localization retains the supplied unit component. -/
@[simp] theorem unit_app_Q (A : CochainComplex Y.Modules ℤ) :
    (unit f).app (DerivedCategory.Q.obj A) = unitOnCochain f A := by
  simp [unit, Localization.liftNatTrans_app, unitOnCochains]

/-- Localization retains the supplied counit component. -/
@[simp] theorem counit_app_Q (B : CochainComplex X.Modules ℤ) :
    (counit f).app (DerivedCategory.Q.obj B) = counitOnCochain f B := by
  simp [counit, Localization.liftNatTrans_app, counitOnCochains]

/-- The first triangle law for the specified maps. -/
theorem left_triangle :
    Functor.whiskerRight (unit f) (L(f)^*) ≫
        (Functor.associator (L(f)^*) (R(f)_*) (L(f)^*)).hom ≫
        Functor.whiskerLeft (L(f)^*) (counit f) =
      NatTrans.id (𝟭 _ ⋙ L(f)^*) := sorry

/-- The second triangle law for the specified maps. -/
theorem right_triangle :
    Functor.whiskerLeft (R(f)_*) (unit f) ≫
        (Functor.associator (R(f)_*) (L(f)^*) (R(f)_*)).inv ≫
        Functor.whiskerRight (counit f) (R(f)_*) =
      NatTrans.id (R(f)_* ⋙ 𝟭 _) := sorry

end DerivedAdjunction

/-- The unbounded adjunction constructed from actual augmentations and the ordinary adjunction.
No absolute-derived pair certificate is an input. -/
@[stacks 079W]
def moduleDerivedAdjunction {X Y : RingedSpace.{u}} (f : X ⟶ Y) : L(f)^* ⊣ R(f)_* :=
  Adjunction.mkOfUnitCounit {
    unit := DerivedAdjunction.unit f
    counit := DerivedAdjunction.counit f
    left_triangle := DerivedAdjunction.left_triangle f
    right_triangle := DerivedAdjunction.right_triangle f }

section Compatibility
variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)
variable [CategoryWithHomology (RingedSpace.Modules X)]
variable [CategoryWithHomology (RingedSpace.Modules Y)]
variable [(pushforward f).Additive] [(pullback f).Additive]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
variable [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Legacy name for the explicit absolute-derived pair input. -/
abbrev DerivedAdjunction.HasPair : Prop :=
  @RingedSite.Hom.DerivedAdjunction.HasPair _ _ (opensRingedSiteHom f)
    _ _ _ (opensRingedSiteHom.DerivedPushforward.hasDerived f) _

/-- Compatibility wrapper retaining the old explicit argument list.
The pair proof is unused: all maps come from `moduleDerivedAdjunction`. -/
abbrev modulePullbackDerivedPushforwardAdjunction [h : DerivedAdjunction.HasPair f] :
    L(f)^* ⊣ R(f)_* := moduleDerivedAdjunction f
end Compatibility

/-- The actual unbounded derived functors form an adjoint pair. -/
@[stacks 079W]
theorem modulePullbackDerivedPushforward_isAdjoint {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    Functor.IsLeftAdjoint (L(f)^*) ∧ Functor.IsRightAdjoint (R(f)_*) :=
  ⟨(moduleDerivedAdjunction f).isLeftAdjoint, (moduleDerivedAdjunction f).isRightAdjoint⟩

/-- Derived inverse image along any ringed-space morphism is a left adjoint. -/
@[stacks 079W]
instance modulePullbackDerived_isLeftAdjoint {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (L(f)^*).IsLeftAdjoint := (moduleDerivedAdjunction f).isLeftAdjoint

/-- Derived direct image along any ringed-space morphism is a right adjoint. -/
instance modulePushforwardDerived_isRightAdjoint {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (R(f)_*).IsRightAdjoint := (moduleDerivedAdjunction f).isRightAdjoint

end AlgebraicGeometry.RingedSpace
