/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.AtlasRinged
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived
public import ReasLib.AlgebraicGeometry.RingedSite.Module.InverseImage.Exact
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact

/-! # Module comparisons for atlas ringed sites -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig
open RingedSite.Hom RingedSite.Cocontinuous

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale.Atlas

variable {S : Scheme.{u}}

/-- Underlying module inverse image `i_f^*` with coefficients `𝒪_Y`, via `i_f^♯`. -/
noncomputable def relocalizationModuleFunctor {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    RingedSite.ModuleCat.{u + 1} (overEtaleRingedSite X) ⥤
      RingedSite.ModuleCat.{u + 1} (ringedSite Y) :=
  moduleInverseImage (relocalizationFunctor f) (overEtaleStructureSheaf X) ⋙
    SheafOfModules.restrictScalars.{u + 1} (smallToBigStructureSheafMap f)

/-- `relocalizationModuleFunctor f` is module inverse image along `i_f` followed by
restriction of scalars along `i_f^♯`. -/
theorem relocalizationModuleFunctor_eq {X Y : AlgebraicSpace S} (f : Y ⟶ X) :
    relocalizationModuleFunctor f =
      moduleInverseImage (relocalizationFunctor f) (overEtaleStructureSheaf X) ⋙
        SheafOfModules.restrictScalars.{u + 1} (smallToBigStructureSheafMap f) :=
  rfl

/-- `relocalizationModuleFunctor f` preserves finite limits. -/
instance relocalizationModuleFunctor_preservesFiniteLimits {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) :
    PreservesFiniteLimits (relocalizationModuleFunctor f) :=
  sorry

/-- `relocalizationModuleFunctor f` preserves finite colimits. -/
instance relocalizationModuleFunctor_preservesFiniteColimits {X Y : AlgebraicSpace S}
    (f : Y ⟶ X) :
    PreservesFiniteColimits (relocalizationModuleFunctor f) :=
  sorry

/-- Derived inverse image `i_f^* : D((Spaces/X)_étale, 𝒪) ⥤ D(Y_étale, 𝒪_Y)`. -/
noncomputable def relocalizationModuleDerived {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [UnivLE.{u + 1, u + 1}] :
    ModuleDerived.{u + 1} (overEtaleRingedSite X) ⥤
      ModuleDerived.{u + 1} (ringedSite Y) :=
  @ExactFunctor.mapDerivedCategory
    (RingedSite.ModuleCat.{u + 1} (overEtaleRingedSite X)) _ _
    (moduleCat_hasDerivedCategory (overEtaleRingedSite X))
    (RingedSite.ModuleCat.{u + 1} (ringedSite Y)) _ _
    (moduleCat_hasDerivedCategory (ringedSite Y))
    (ExactFunctor.of (relocalizationModuleFunctor f))

/-- The composite of derived pullback to the big étale site with derived relocalization. -/
noncomputable def etaleSmallModulePullbackDerived {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [UnivLE.{u + 1, u + 1}]
    [(etalePiRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint]
    [Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{u + 1} (etalePiRingedHom X))
      (ModuleQis.{u + 1} (ringedSite X))] :
    ModuleDerived.{u + 1} (ringedSite X) ⥤ ModuleDerived.{u + 1} (ringedSite Y) :=
  modulePullbackDerived.{u + 1} (etalePiRingedHom X) ⋙ relocalizationModuleDerived f

/-- `etaleSmallModulePullbackDerived f` is the composite `i_f^* ∘ Lπ_X^*`. -/
theorem etaleSmallModulePullbackDerived_eq {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [UnivLE.{u + 1, u + 1}]
    [(etalePiRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint]
    [Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{u + 1} (etalePiRingedHom X))
      (ModuleQis.{u + 1} (ringedSite X))] :
    etaleSmallModulePullbackDerived f =
      modulePullbackDerived.{u + 1} (etalePiRingedHom X) ⋙
        relocalizationModuleDerived f :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Etale.Atlas

end

end
