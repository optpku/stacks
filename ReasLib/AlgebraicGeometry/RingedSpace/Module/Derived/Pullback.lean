module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Localization.Triangulated
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpensRingedSite
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced
public import ReasLib.CategoryTheory.DerivedCategory.Functor.CellModel
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry.RingedSpace.Hom

/-!
# Derived pullback of modules on ringed spaces

This module owns the homotopy-level inverse-image functor and its unbounded total left derived
functor for morphisms of ringed spaces.
-/

open CategoryTheory
open ComplexShape
open AlgebraicGeometry
open scoped RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The quasi-isomorphisms used to localize the homotopy category of module sheaves on a ringed
space. -/
abbrev ModuleQis (X : RingedSpace.{u}) :=
  HomotopyCategory.quasiIso (RingedSpace.Modules X) (up ℤ)

/-- The homotopy-to-derived functor induced by module pullback along a morphism of ringed spaces.
-/
abbrev modulePullbackToDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(pullback f).Additive] :
    HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤
      DerivedCategory (RingedSpace.Modules X) :=
  Functor.Homotopy.toDerived (pullback f)

namespace ModulePullbackCells

/-- Ordinary ringed-space inverse image preserves quasi-isomorphisms between the specified
K-flat sheaf-cell models. The original map and its quasi-isomorphism premise are retained. -/
theorem modelMap_quasiIso {X Y : RingedSpace.{u}} (f : X ⟶ Y) [(pullback f).Additive]
    {A B : CochainComplex Y.Modules ℤ} (a : A ⟶ B) (ha : QuasiIso a) :
    QuasiIso (((pullback f).mapHomologicalComplex (up ℤ)).map
      (SheafOfModules.CellReplacement.modelMap a)) := sorry

/-- The native localizing functor inverts the actual pulled-back cell-model maps. -/
theorem cochain_inverts {X Y : RingedSpace.{u}} (f : X ⟶ Y) [(pullback f).Additive] :
    (HomologicalComplex.quasiIso Y.Modules (up ℤ)).IsInvertedBy
      (Functor.CellModel.cochain (pullback f)) := by
  intro A B a ha
  letI := modelMap_quasiIso f a ha
  change IsIso ((DerivedCategory.Q (C := X.Modules)).map
    (((pullback f).mapHomologicalComplex (up ℤ)).map
      (SheafOfModules.CellReplacement.modelMap a)))
  infer_instance

/-- The augmentation at an actual K-flat cell model remains a quasi-isomorphism after
ordinary inverse image. This is the acyclicity law used in the universal property. -/
theorem modelAugmentation_quasiIso {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(pullback f).Additive] (A : CochainComplex Y.Modules ℤ) :
    QuasiIso (((pullback f).mapHomologicalComplex (up ℤ)).map
      (SheafOfModules.CellReplacement.augmentation (SheafOfModules.CellReplacement.model A))) :=
  sorry

/-- Localizing that specified model augmentation supplies the required acyclicity certificate. -/
theorem modelAugmentation_isIso {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(pullback f).Additive] (A : CochainComplex Y.Modules ℤ) :
    IsIso ((Functor.CellModel.ordinaryCochain (pullback f)).map
      (SheafOfModules.CellReplacement.augmentation (SheafOfModules.CellReplacement.model A))) := by
  letI := modelAugmentation_quasiIso f A
  change IsIso ((DerivedCategory.Q (C := X.Modules)).map
    (((pullback f).mapHomologicalComplex (up ℤ)).map
      (SheafOfModules.CellReplacement.augmentation (SheafOfModules.CellReplacement.model A))))
  infer_instance

end ModulePullbackCells

/-- Module pullback on homotopy categories admits an everywhere defined total left derived functor.
-/
theorem modulePullbackToDerived_hasLeftDerivedFunctor
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)]
    [CategoryWithHomology (RingedSpace.Modules Y)]
    [(pullback f).Additive] :
    (modulePullbackToDerived f).HasLeftDerivedFunctor (ModuleQis Y) :=
  Functor.CellModel.hasLeftDerivedHomotopy (pullback f)
    (ModulePullbackCells.cochain_inverts f) (ModulePullbackCells.modelAugmentation_isIso f)

/-- The canonical total-left-derived-functor instance for module pullback. -/
instance instModulePullbackToDerivedHasLeftDerivedFunctor
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)]
    [CategoryWithHomology (RingedSpace.Modules Y)]
    [(pullback f).Additive] :
    Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y) :=
  modulePullbackToDerived_hasLeftDerivedFunctor f

/-- The generic homotopy-to-derived spelling of module pullback admits the same total-left-derived
functor instance.  This bridge lets generic derived-composition APIs apply directly to ringed
spaces. -/
instance instPullbackToDerivedHasLeftDerivedFunctor
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)]
    [CategoryWithHomology (RingedSpace.Modules Y)]
    [(pullback f).Additive] :
    Functor.HasLeftDerivedFunctor
      (Functor.Homotopy.toDerived (pullback f))
      (HomotopyCategory.quasiIso (RingedSpace.Modules Y) (up ℤ)) :=
  modulePullbackToDerived_hasLeftDerivedFunctor f

/-- The opens-ringed-site presentation of module pullback has a total-left-derived functor. -/
@[instance]
theorem opensRingedSiteHom_modulePullbackToDerived_hasLeftDerivedFunctor
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)]
    [CategoryWithHomology (RingedSpace.Modules Y)]
    [(pullback f).Additive]
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    Functor.HasLeftDerivedFunctor
      (RingedSite.Hom.modulePullbackToDerived (opensRingedSiteHom f))
      (RingedSite.Hom.ModuleQis (opensRingedSite Y)) :=
  modulePullbackToDerived_hasLeftDerivedFunctor f

namespace OpensModulePullbackCells

/-- The composite inverse image preserves quasi-isomorphisms between the specified flat-term
K-flat cell models on the original opens site. -/
theorem compModelMap_quasiIso {X Y Z : RingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {A B : CochainComplex Z.Modules ℤ} (a : A ⟶ B) (ha : QuasiIso a) :
    QuasiIso (((RingedSite.Hom.modulePullback
      (RingedSite.Hom.comp (opensRingedSiteHom f) (opensRingedSiteHom g))).mapHomologicalComplex
        (up ℤ)).map (SheafOfModules.CellReplacement.modelMap a)) := sorry

/-- Localization inverts those actual composite-pullback model maps. -/
theorem compCochain_inverts {X Y Z : RingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (HomologicalComplex.quasiIso Z.Modules (up ℤ)).IsInvertedBy
      (Functor.CellModel.cochain (RingedSite.Hom.modulePullback
        (RingedSite.Hom.comp (opensRingedSiteHom f) (opensRingedSiteHom g)))) := by
  intro A B a ha
  letI := compModelMap_quasiIso f g a ha
  change IsIso ((DerivedCategory.Q (C := X.Modules)).map
    (((RingedSite.Hom.modulePullback
      (RingedSite.Hom.comp (opensRingedSiteHom f) (opensRingedSiteHom g))).mapHomologicalComplex
        (up ℤ)).map (SheafOfModules.CellReplacement.modelMap a)))
  infer_instance

/-- The augmentation at a specified K-flat model stays a quasi-isomorphism under the actual
composite inverse image. -/
theorem compModelAugmentation_quasiIso {X Y Z : RingedSpace.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (A : CochainComplex Z.Modules ℤ) :
    QuasiIso (((RingedSite.Hom.modulePullback
      (RingedSite.Hom.comp (opensRingedSiteHom f) (opensRingedSiteHom g))).mapHomologicalComplex
        (up ℤ)).map (SheafOfModules.CellReplacement.augmentation
          (SheafOfModules.CellReplacement.model A))) := sorry

/-- The specified augmentation supplies the acyclicity input to the actual cell universal map. -/
theorem compModelAugmentation_isIso {X Y Z : RingedSpace.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (A : CochainComplex Z.Modules ℤ) :
    IsIso ((Functor.CellModel.ordinaryCochain (RingedSite.Hom.modulePullback
      (RingedSite.Hom.comp (opensRingedSiteHom f) (opensRingedSiteHom g)))).map
        (SheafOfModules.CellReplacement.augmentation
          (SheafOfModules.CellReplacement.model A))) := by
  letI := compModelAugmentation_quasiIso f g A
  change IsIso ((DerivedCategory.Q (C := X.Modules)).map
    (((RingedSite.Hom.modulePullback
      (RingedSite.Hom.comp (opensRingedSiteHom f) (opensRingedSiteHom g))).mapHomologicalComplex
        (up ℤ)).map (SheafOfModules.CellReplacement.augmentation
          (SheafOfModules.CellReplacement.model A))))
  infer_instance

end OpensModulePullbackCells

/-- Pullback along a composite of opens-ringed-site morphisms has a total-left-derived functor. -/
theorem opensRingedSiteHom_comp_modulePullbackToDerived_hasLeftDerivedFunctor
    {X Y Z : RingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [CategoryWithHomology (RingedSpace.Modules X)]
    [CategoryWithHomology (RingedSpace.Modules Y)]
    [CategoryWithHomology (RingedSpace.Modules Z)]
    [(pullback f).Additive] [(pullback g).Additive]
    [HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    Functor.HasLeftDerivedFunctor
      (RingedSite.Hom.modulePullbackToDerived
        (RingedSite.Hom.comp (opensRingedSiteHom f) (opensRingedSiteHom g)))
      (RingedSite.Hom.ModuleQis (opensRingedSite Z)) :=
  Functor.CellModel.hasLeftDerivedHomotopy
    (RingedSite.Hom.modulePullback
      (RingedSite.Hom.comp (opensRingedSiteHom f) (opensRingedSiteHom g)))
    (OpensModulePullbackCells.compCochain_inverts f g)
    (OpensModulePullbackCells.compModelAugmentation_isIso f g)

/-- The unbounded derived pullback functor `Lf^*` on module sheaves over ringed spaces. -/
noncomputable def modulePullbackDerived
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)]
    [CategoryWithHomology (RingedSpace.Modules Y)]
    [(pullback f).Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)] :
    DerivedCategory (RingedSpace.Modules Y) ⥤ DerivedCategory (RingedSpace.Modules X) :=
  (modulePullbackToDerived f).totalLeftDerived DerivedCategory.Qh (ModuleQis Y)

namespace modulePullbackDerived

/-- Derived pullback is the total left derived functor of pullback on module sheaves. The canonical
homology, additivity, and derived-functor instances are inferred from the ringed spaces and their
morphism. -/
@[stacks 08DE "derived pullback universal property", instance]
theorem isLeftDerivedFunctor {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (modulePullbackDerived f).IsLeftDerivedFunctor
      ((modulePullbackToDerived f).totalLeftDerivedCounit DerivedCategory.Qh (ModuleQis Y))
      (ModuleQis Y) := by
  change ((modulePullbackToDerived f).totalLeftDerived DerivedCategory.Qh (ModuleQis Y)).IsLeftDerivedFunctor
    ((modulePullbackToDerived f).totalLeftDerivedCounit DerivedCategory.Qh (ModuleQis Y)) (ModuleQis Y)
  infer_instance

end modulePullbackDerived

/-- The public total-derived pullback and the actual cell producer are compared by native
uniqueness, with both universal witnesses backed by the constructed cell-model lift. -/
noncomputable def modulePullbackDerivedCellIso {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(pullback f).Additive] :
    Functor.CellModel.derived (pullback f) (ModulePullbackCells.cochain_inverts f) ≅
      modulePullbackDerived f := by
  letI := modulePullbackDerived.isLeftDerivedFunctor f
  exact Functor.CellModel.isoOfHomotopyModel (pullback f) (ModulePullbackCells.cochain_inverts f)
    (ModulePullbackCells.modelAugmentation_isIso f) (modulePullbackDerived f)
    ((modulePullbackToDerived f).totalLeftDerivedCounit DerivedCategory.Qh (ModuleQis Y))


end AlgebraicGeometry.RingedSpace

namespace RingedSpaceDerivedPullback

/-- Notation for unbounded derived pullback on modules over a ringed space. -/
scoped notation:max "L(" f ")" "^*" =>
  AlgebraicGeometry.RingedSpace.modulePullbackDerived f

end RingedSpaceDerivedPullback
