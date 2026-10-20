/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.ModuleComparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Derived.Adjunction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.GlobalSections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.DirectImage
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.Underlying
public import ReasLib.CategoryTheory.Sites.Derived.InverseImage
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain

/-!
# Big and small étale derived cohomology of algebraic spaces

Cohomology over an object of the big étale site agrees with small étale cohomology
after geometric inverse image or derived module pullback.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig
open CategoryTheory.Functor.RightDerived
open RingedSite.Hom.ModuleSections.Underlying
open RingedSite.Hom RingedSite.Cocontinuous

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale.Derived

variable {S : Scheme.{u}}

/-- Big étale cohomology of geometric inverse image agrees with small étale cohomology. -/
theorem etaleCohomology_piInverseImage (X : AlgebraicSpace S) (n : ℤ)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (overEtaleTopology X) AddCommGrpCat.{u + 1}]
    [IsGrothendieckAbelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [IsGrothendieckAbelian (Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1})]
    [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (relocalizationFunctor (𝟙 X)).op.HasLeftKanExtension P]
    [Functor.HasRightDerivedFunctor
      (Cochain.toDerived (globalSections X))
      (HomologicalComplex.quasiIso
        (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) (ComplexShape.up ℤ))]
    (K : DerivedCategory (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((siteAbelianSectionsDerived (overEtaleTopology X) (Over.mk (𝟙 X))).obj
          ((etalePiInverseImage X).mapDerivedCategory.obj K)))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((Cochain.functor (globalSections X)).obj K)) :=
  sorry

/-- Big étale module cohomology of derived pullback agrees with small étale module cohomology. -/
theorem etaleModuleCohomology_piPullback (X : AlgebraicSpace S) (n : ℤ)
    [UnivLE.{u + 1, u + 1}]
    [HasWeakSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasGlobalSectionsFunctor (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1} (ringedSite X))]
    [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1} (Big.ringedSite X))]
    [(etalePiModulePushforward X).IsRightAdjoint]
    [Functor.HasLeftDerivedFunctor
      (etalePiModuleToDerived X)
      (ModuleQis.{u + 1} (ringedSite X))]
    (K : ModuleDerived.{u + 1} (ringedSite X)) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((sectionsDerived.{u + 1} (Big.ringedSite X) (Over.mk (𝟙 X))).obj
          ((etalePiModulePullbackDerived X).obj K)))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((moduleGlobalSectionsDerived.{u + 1} (ringedSite X)).obj K)) :=
  sorry

/-- Big étale cohomology over a morphism agrees with cohomology of its small inverse image. -/
theorem etaleCohomology_smallInverseImage {X Y : AlgebraicSpace S} (f : Y ⟶ X) (n : ℤ)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [HasSheafify (overEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasWeakSheafify (spacesEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [IsGrothendieckAbelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [IsGrothendieckAbelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
    [IsGrothendieckAbelian (Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1})]
    [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (relocalizationFunctor (𝟙 X)).op.HasLeftKanExtension P]
    [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (etaleBaseChange f).op.HasLeftKanExtension P]
    [PreservesFiniteLimits (sheafInverseImage AddCommGrpCat.{u + 1} f)]
    [PreservesFiniteColimits (sheafInverseImage AddCommGrpCat.{u + 1} f)]
    [(sheafInverseImage AddCommGrpCat.{u + 1} f).Additive]
    [Functor.HasRightDerivedFunctor
      (Cochain.toDerived (globalSections Y))
      (HomologicalComplex.quasiIso
        (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) (ComplexShape.up ℤ))]
    (K : DerivedCategory (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((siteAbelianSectionsDerived (overEtaleTopology X) (Over.mk f)).obj
          ((etalePiInverseImage X).mapDerivedCategory.obj K)))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((Cochain.functor (globalSections Y)).obj
          ((sheafInverseImage AddCommGrpCat.{u + 1} f).mapDerivedCategory.obj K))) :=
  sorry

/-- Big étale module cohomology over a morphism agrees with cohomology of its derived small pullback. -/
theorem etaleModuleCohomology_smallPullback {X Y : AlgebraicSpace S} (f : Y ⟶ X) (n : ℤ)
    [UnivLE.{u + 1, u + 1}]
    [HasWeakSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [HasGlobalSectionsFunctor (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1} (ringedSite X))]
    [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1} (Big.ringedSite X))]
    [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1} (ringedSite Y))]
    [(etalePiModulePushforward X).IsRightAdjoint]
    [Functor.HasLeftDerivedFunctor
      (etalePiModuleToDerived X)
      (ModuleQis.{u + 1} (ringedSite X))]
    [(SheafOfModules.pushforward.{u + 1} (smallChartStructureMap Y)).IsRightAdjoint]
    [(etaleSmallModulePushforward f).IsRightAdjoint]
    [Functor.HasLeftDerivedFunctor (etaleSmallModuleToDerived f)
      (ModuleQis.{u + 1} (ringedSite X))]
    (K : ModuleDerived.{u + 1} (ringedSite X)) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((sectionsDerived.{u + 1} (Big.ringedSite X) (Over.mk f)).obj
          ((etalePiModulePullbackDerived X).obj K)))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((moduleGlobalSectionsDerived.{u + 1} (ringedSite Y)).obj
          ((etaleSmallModulePullbackDerived f).obj K))) :=
  sorry

/-- Big étale cohomology agrees with small étale cohomology after relocalization. -/
theorem etaleCohomology_relocalization {X Y : AlgebraicSpace S} (f : Y ⟶ X) (n : ℤ)
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [HasSheafify (overEtaleTopology X) AddCommGrpCat.{u + 1}]
    [IsGrothendieckAbelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
    [IsGrothendieckAbelian (Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Functor.HasRightDerivedFunctor
      (Cochain.toDerived (globalSections Y))
      (HomologicalComplex.quasiIso
        (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) (ComplexShape.up ℤ))]
    (M : DerivedCategory (Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1})) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((siteAbelianSectionsDerived (overEtaleTopology X) (Over.mk f)).obj M))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((Cochain.functor (globalSections Y)).obj
          ((siteAbelianInverseImageDerived (smallEtaleTopology Y)
            (overEtaleTopology X) (relocalizationFunctor f)).obj M))) :=
  sorry

/-- Big étale module cohomology agrees with small étale module cohomology after relocalization. -/
theorem etaleModuleCohomology_relocalization {X Y : AlgebraicSpace S} (f : Y ⟶ X) (n : ℤ)
    [UnivLE.{u + 1, u + 1}]
    [HasWeakSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [HasGlobalSectionsFunctor (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1} (ringedSite Y))]
    [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1} (Big.ringedSite X))]
    (M : ModuleDerived.{u + 1} (Big.ringedSite X)) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((sectionsDerived.{u + 1} (Big.ringedSite X) (Over.mk f)).obj M))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((moduleGlobalSectionsDerived.{u + 1} (ringedSite Y)).obj
          ((relocalizationModuleDerived f).obj M))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Etale.Derived
