/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.FiberCartesian
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.Exactness
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Restriction
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Pullback.Complex.Monoidal
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.LeftDerived
public import ReasLib.Algebra.Homology.DerivedCategory.Adjunction

set_option backward.privateInPublic true

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor RingedSite
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v w

namespace CategoryTheory.Grothendieck.ModuleDerived

/-- The exact derived action in the standard module-category localizations. -/
private abbrev mapExact {X Y : RingedSite.{u, v, w}} [UnivLE.{max u v, w}]
    (F : SheafOfModules.{w} X.structureSheaf ⥤ₑ SheafOfModules.{w} Y.structureSheaf) :
    Hom.ModuleDerived.{w} X ⥤ Hom.ModuleDerived.{w} Y :=
  @ExactFunctor.mapDerivedCategory _ _ _ (Hom.moduleCat_hasDerivedCategory X)
    _ _ _ (Hom.moduleCat_hasDerivedCategory Y) F

/-- Localization of a transformation of exact module functors in the standard derived models. -/
private def mapExactNat {X Y : RingedSite.{u, v, w}} [UnivLE.{max u v, w}]
    (F G : SheafOfModules.{w} X.structureSheaf ⥤ₑ SheafOfModules.{w} Y.structureSheaf)
    (α : F.obj ⟶ G.obj) : mapExact F ⟶ mapExact G :=
  @ExactFunctor.MapDerivedCategory.map _ _ _ (Hom.moduleCat_hasDerivedCategory X)
    _ _ _ (Hom.moduleCat_hasDerivedCategory Y) F G (ObjectProperty.homMk α)

/-- Composition comparison in the standard derived categories of modules. -/
private def mapExactCompIso {X Y Z : RingedSite.{u, v, w}} [UnivLE.{max u v, w}]
    (F : SheafOfModules.{w} X.structureSheaf ⥤ₑ SheafOfModules.{w} Y.structureSheaf)
    (G : SheafOfModules.{w} Y.structureSheaf ⥤ₑ SheafOfModules.{w} Z.structureSheaf) :
    mapExact (F.comp G) ≅ mapExact F ⋙ mapExact G :=
  @ExactFunctor.MapDerivedCategory.compFunctorIso
    _ _ _ (Hom.moduleCat_hasDerivedCategory X) _ _ _ (Hom.moduleCat_hasDerivedCategory Y)
    _ _ _ (Hom.moduleCat_hasDerivedCategory Z) F G

/-- An exact module adjunction descends to the standard derived localizations. -/
private def mapExactAdjunction {X Y : RingedSite.{u, v, w}} [UnivLE.{max u v, w}]
    (F : SheafOfModules.{w} X.structureSheaf ⥤ₑ SheafOfModules.{w} Y.structureSheaf)
    (G : SheafOfModules.{w} Y.structureSheaf ⥤ₑ SheafOfModules.{w} X.structureSheaf)
    (adj : F.obj ⊣ G.obj) : mapExact F ⊣ mapExact G :=
  @Adjunction.mapDerivedCategory _ _ _ (Hom.moduleCat_hasDerivedCategory X)
    _ _ _ (Hom.moduleCat_hasDerivedCategory Y) F.obj G.obj
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance adj

variable (C : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [IsFiberwiseSite C J]
variable [UnivLE.{max u v, w}]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [HasSheafify (topology C J) (Type w)]
variable [∀ n, ∀ P : (C.obj (op n))ᵒᵖ ⥤ Type w,
    (ι C (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj (op n))ᵒᵖ ⥤ Type w),
    ((C.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable (O : Sheaf (topology C J) CommRingCat.{w})
variable [(topology C J).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [(topology C J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose
    (forget₂ CommRingCat.{w} RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (fiberStageMorphism C J (Sheaf.ringSheafOfComm O) n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (fiberRingedToposMap C J (Sheaf.ringSheafOfComm O) φ).structureMap).IsRightAdjoint]
variable [∀ n, ToposHom.HasModulePullbackDerived
    (fiberStageMorphism C J (Sheaf.ringSheafOfComm O) n)]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived
      (fiberRingedToposMap C J (Sheaf.ringSheafOfComm O) φ)]
variable [(topology C J).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ n, ((J n).toGrothendieck).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Geometric restriction with the restricted structure sheaf is an exact module functor. -/
def componentExact (n : SimplexCategory) :
    SheafOfModules.{w} (Sheaf.ringSheafOfComm O) ⥤ₑ
      SheafOfModules.{w} (fiberComponentRingSheaf C J (Sheaf.ringSheafOfComm O) n) :=
  ⟨moduleComponent C J (Sheaf.ringSheafOfComm O) n,
    @ToposHom.IsFlat.pullback_exact _ _ inferInstance inferInstance
      (fiberStageMorphism C J (Sheaf.ringSheafOfComm O) n) inferInstance
      (Cocontinuous.restrictionMorphism_isFlat
        (fiberTotalRingedSite C J (Sheaf.ringSheafOfComm O)) (J (op n)).toGrothendieck (ι C (op n)))⟩

/-- Exact restriction on derived categories agrees canonically with total left-derived restriction. -/
def derivedComponentIso (n : SimplexCategory) :
    mapExact (X := fiberTotalRingedSite C J (Sheaf.ringSheafOfComm O))
    (Y := fiberComponentRingedSite C J (Sheaf.ringSheafOfComm O) n) (componentExact C J O n) ≅
      moduleDerivedComponent C J (Sheaf.ringSheafOfComm O) n :=
  let f := fiberStageMorphism C J (Sheaf.ringSheafOfComm O) n
  let ε := (ToposHom.modulePullbackToDerived f).totalLeftDerivedCounit
    (Hom.moduleLocalization (fiberTotalRingedSite C J (Sheaf.ringSheafOfComm O)))
    (Hom.ModuleQis (fiberTotalRingedSite C J (Sheaf.ringSheafOfComm O)))
  let hLF := inferInstanceAs
    (f.modulePullbackDerived.IsLeftDerivedFunctor ε
      (Hom.ModuleQis (fiberTotalRingedSite C J (Sheaf.ringSheafOfComm O))))
  @ExactFunctor.LeftDerived.comparisonIso
    _ _ _ (Hom.moduleCat_hasDerivedCategory (fiberTotalRingedSite C J (Sheaf.ringSheafOfComm O)))
    _ _ _ (Hom.moduleCat_hasDerivedCategory (fiberComponentRingedSite C J (Sheaf.ringSheafOfComm O) n))
    (componentExact C J O n) f.modulePullbackDerived ε hLF
    (@ExactFunctor.LeftDerived.comparison_isIso
      _ _ _ (Hom.moduleCat_hasDerivedCategory (fiberTotalRingedSite C J (Sheaf.ringSheafOfComm O)))
      _ _ _ (Hom.moduleCat_hasDerivedCategory (fiberComponentRingedSite C J (Sheaf.ringSheafOfComm O) n))
      (componentExact C J O n) f.modulePullbackDerived ε hLF)

/-- Lower shriek is left adjoint to geometric restriction of modules. -/
private def underivedAdjunction (n : SimplexCategory) :
    fiberModuleLowerShriek C J (Sheaf.ringSheafOfComm O) n ⊣
      (componentExact C J O n).obj :=
  (fiberModuleLowerShriek.adjunction C J (Sheaf.ringSheafOfComm O) n).ofNatIsoRight
    (fiberModuleInverseImageIsoModulePullback C J (Sheaf.ringSheafOfComm O) n)

/-- The restriction mate formed from the structure-module unit and canonical pullback tensorator. -/
def shriekTensorMate (n : SimplexCategory)
    (F : SheafOfModules.{w} (Sheaf.ringSheafOfComm O)) :
    (componentExact C J O n).obj.obj F ⟶
      (componentExact C J O n).obj.obj
        ((fiberModuleLowerShriek C J (Sheaf.ringSheafOfComm O) n).obj
          (SheafOfModules.RingedSite.unitModule (J (op n)).toGrothendieck
            ((fiberRestrict C J CommRingCat.{w} n).obj O)) ⊗ F) :=
  let U := SheafOfModules.RingedSite.unitModule (J (op n)).toGrothendieck
    ((fiberRestrict C J CommRingCat.{w} n).obj O)
  let L := fiberModuleLowerShriek C J (Sheaf.ringSheafOfComm O) n
  let R := (componentExact C J O n).obj
  let Oₙ := (fiberRestrict C J CommRingCat.{w} n).obj O
  let M := SheafOfModules.RingedSite.ringedSiteModuleCategory (J (op n)).toGrothendieck Oₙ
  (leftUnitor (C := M) (R.obj F)).inv ≫
    tensorHom (C := M) (SheafOfModules.RingedSite.unitIsoTensorUnit
      (J := (J (op n)).toGrothendieck) (𝒪 := Oₙ)).inv (𝟙 (R.obj F)) ≫
    tensorHom (C := M) ((underivedAdjunction C J O n).unit.app U) (𝟙 (R.obj F)) ≫
    ((ToposHom.modulePullback.coreMonoidal (OX := Oₙ) (OY := O)
      (fiberStageMorphism C J (Sheaf.ringSheafOfComm O) n)).μIso (L.obj U) F).hom

/-- The lower-shriek tensor comparison is the adjunct of the canonical structure-module mate. -/
def shriekTensorHom (n : SimplexCategory)
    (F : SheafOfModules.{w} (Sheaf.ringSheafOfComm O)) :
    (fiberModuleLowerShriek C J (Sheaf.ringSheafOfComm O) n).obj
        ((componentExact C J O n).obj.obj F) ⟶
      (fiberModuleLowerShriek C J (Sheaf.ringSheafOfComm O) n).obj
        (SheafOfModules.RingedSite.unitModule (J (op n)).toGrothendieck
          ((fiberRestrict C J CommRingCat.{w} n).obj O)) ⊗ F :=
  ((underivedAdjunction C J O n).homEquiv _ _).symm (shriekTensorMate C J O n F)

variable (h_flat : ∀ {n m : SimplexCategory} (φ : n ⟶ m),
  ToposHom.IsFlat (fiberRingedToposMap C J (Sheaf.ringSheafOfComm O) φ))

/-- Module lower shriek is exact when all simplex structure maps are flat. -/
def lowerShriekExact (n : SimplexCategory) :
    SheafOfModules.{w} (fiberComponentRingSheaf C J (Sheaf.ringSheafOfComm O) n) ⥤ₑ
      SheafOfModules.{w} (Sheaf.ringSheafOfComm O) :=
  ⟨fiberModuleLowerShriek C J (Sheaf.ringSheafOfComm O) n,
    fiberModuleLowerShriek_exact C J (Sheaf.ringSheafOfComm O) n (fun φ ↦ h_flat φ)⟩

/-- Exact module lower shriek on unbounded derived categories. -/
def lowerShriek (n : SimplexCategory) :
    Hom.ModuleDerived.{w} (fiberComponentRingedSite C J (Sheaf.ringSheafOfComm O) n) ⥤
      Hom.ModuleDerived.{w} (fiberTotalRingedSite C J (Sheaf.ringSheafOfComm O)) :=
  mapExact (X := fiberComponentRingedSite C J (Sheaf.ringSheafOfComm O) n)
    (Y := fiberTotalRingedSite C J (Sheaf.ringSheafOfComm O)) (lowerShriekExact C J O h_flat n)

/-- Derived lower shriek is left adjoint to the canonical total left-derived restriction. -/
def lowerShriekAdjunction (n : SimplexCategory) :
    lowerShriek C J O h_flat n ⊣ moduleDerivedComponent C J (Sheaf.ringSheafOfComm O) n :=
  (mapExactAdjunction (X := fiberComponentRingedSite C J (Sheaf.ringSheafOfComm O) n)
    (Y := fiberTotalRingedSite C J (Sheaf.ringSheafOfComm O)) (lowerShriekExact C J O h_flat n) (componentExact C J O n)
    (underivedAdjunction C J O n)).ofNatIsoRight (derivedComponentIso C J O n)

include h_flat in
/-- Tensoring with the lower-shriek structure module is exact under flat simplex structure maps. -/
theorem shriekUnitTensor_exact (n : SimplexCategory) :
    exactFunctor (SheafOfModules.{w} (Sheaf.ringSheafOfComm O))
      (SheafOfModules.{w} (Sheaf.ringSheafOfComm O))
      (tensorLeft ((fiberModuleLowerShriek C J (Sheaf.ringSheafOfComm O) n).obj
        (SheafOfModules.RingedSite.unitModule (J (op n)).toGrothendieck
          ((fiberRestrict C J CommRingCat.{w} n).obj O)))) := sorry

/-- Exact tensoring with the flat lower-shriek structure module. -/
def shriekUnitTensorExact (n : SimplexCategory) :
    SheafOfModules.{w} (Sheaf.ringSheafOfComm O) ⥤ₑ
      SheafOfModules.{w} (Sheaf.ringSheafOfComm O) :=
  ⟨tensorLeft ((fiberModuleLowerShriek C J (Sheaf.ringSheafOfComm O) n).obj
      (SheafOfModules.RingedSite.unitModule (J (op n)).toGrothendieck
        ((fiberRestrict C J CommRingCat.{w} n).obj O))), shriekUnitTensor_exact C J O h_flat n⟩

/-- Derived tensor with the lower-shriek structure module. -/
def shriekUnitTensor (n : SimplexCategory) :
    Hom.ModuleDerived.{w} (fiberTotalRingedSite C J (Sheaf.ringSheafOfComm O)) ⥤
      Hom.ModuleDerived.{w} (fiberTotalRingedSite C J (Sheaf.ringSheafOfComm O)) :=
  mapExact (X := fiberTotalRingedSite C J (Sheaf.ringSheafOfComm O))
    (Y := fiberTotalRingedSite C J (Sheaf.ringSheafOfComm O)) (shriekUnitTensorExact C J O h_flat n)

/-- The structure-module unit-tensor mates form a natural transformation. -/
def shriekTensorMateNatTrans (n : SimplexCategory) :
    (componentExact C J O n).obj ⟶
      (shriekUnitTensorExact C J O h_flat n).obj ⋙ (componentExact C J O n).obj where
  app F := shriekTensorMate C J O n F
  naturality := sorry

/-- The adjunct module tensor comparisons form a natural transformation. -/
def shriekTensorNatTrans (n : SimplexCategory) :
    (componentExact C J O n).obj ⋙ fiberModuleLowerShriek C J (Sheaf.ringSheafOfComm O) n ⟶
      (shriekUnitTensorExact C J O h_flat n).obj where
  app F := shriekTensorHom C J O n F
  naturality := sorry

/-- The canonical derived comparison, with restriction in its total left-derived model. -/
def shriekTensorComparison (n : SimplexCategory)
    (K : Hom.ModuleDerived.{w} (fiberTotalRingedSite C J (Sheaf.ringSheafOfComm O))) :
    (lowerShriek C J O h_flat n).obj
        ((moduleDerivedComponent C J (Sheaf.ringSheafOfComm O) n).obj K) ⟶
      (shriekUnitTensor C J O h_flat n).obj K :=
  (lowerShriek C J O h_flat n).map ((derivedComponentIso C J O n).inv.app K) ≫
    (mapExactCompIso (X := fiberTotalRingedSite C J (Sheaf.ringSheafOfComm O))
      (Y := fiberComponentRingedSite C J (Sheaf.ringSheafOfComm O) n) (Z := fiberTotalRingedSite C J (Sheaf.ringSheafOfComm O))
      (componentExact C J O n) (lowerShriekExact C J O h_flat n)).inv.app K ≫
    (mapExactNat (X := fiberTotalRingedSite C J (Sheaf.ringSheafOfComm O))
      (Y := fiberTotalRingedSite C J (Sheaf.ringSheafOfComm O)) ((componentExact C J O n).comp (lowerShriekExact C J O h_flat n))
      (shriekUnitTensorExact C J O h_flat n) (shriekTensorNatTrans C J O h_flat n)).app K

/-- The localized unit-tensor mate transported to canonical total left-derived restrictions. -/
def shriekTensorDerivedMate (n : SimplexCategory)
    (K : Hom.ModuleDerived.{w} (fiberTotalRingedSite C J (Sheaf.ringSheafOfComm O))) :
    (moduleDerivedComponent C J (Sheaf.ringSheafOfComm O) n).obj K ⟶
      (moduleDerivedComponent C J (Sheaf.ringSheafOfComm O) n).obj
        ((shriekUnitTensor C J O h_flat n).obj K) :=
  (derivedComponentIso C J O n).inv.app K ≫
    (mapExactNat (X := fiberTotalRingedSite C J (Sheaf.ringSheafOfComm O))
      (Y := fiberComponentRingedSite C J (Sheaf.ringSheafOfComm O) n) (componentExact C J O n)
      ((shriekUnitTensorExact C J O h_flat n).comp (componentExact C J O n))
      (shriekTensorMateNatTrans C J O h_flat n)).app K ≫
    (mapExactCompIso (X := fiberTotalRingedSite C J (Sheaf.ringSheafOfComm O))
      (Y := fiberTotalRingedSite C J (Sheaf.ringSheafOfComm O)) (Z := fiberComponentRingedSite C J (Sheaf.ringSheafOfComm O) n)
      (shriekUnitTensorExact C J O h_flat n) (componentExact C J O n)).hom.app K ≫
    (derivedComponentIso C J O n).hom.app ((shriekUnitTensor C J O h_flat n).obj K)

/-- The derived module tensor comparison is characterized by its canonical adjunction mate. -/
theorem shriekTensorComparison_spec (n : SimplexCategory)
    (K : Hom.ModuleDerived.{w} (fiberTotalRingedSite C J (Sheaf.ringSheafOfComm O))) :
    shriekTensorComparison C J O h_flat n K =
      ((lowerShriekAdjunction C J O h_flat n).homEquiv
        ((moduleDerivedComponent C J (Sheaf.ringSheafOfComm O) n).obj K)
        ((shriekUnitTensor C J O h_flat n).obj K)).symm
        (shriekTensorDerivedMate C J O h_flat n K) := sorry

/-- A derived module is cartesian exactly when all canonical shriek-tensor comparisons
are invertible, provided all simplex structure-ring maps are flat. -/
theorem isCartesian_iff_shriekTensor
    (K : Hom.ModuleDerived.{w} (fiberTotalRingedSite C J (Sheaf.ringSheafOfComm O))) :
    IsCartesian C J (Sheaf.ringSheafOfComm O) K ↔
      ∀ n : SimplexCategory, IsIso (shriekTensorComparison C J O h_flat n K) := sorry

end CategoryTheory.Grothendieck.ModuleDerived
