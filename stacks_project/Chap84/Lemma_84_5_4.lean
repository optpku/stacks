/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Derived.CohomologyComparison
import StacksCheckRecall

/-! # Lemma 84.5.4: comparison of big and small étale derived cohomology -/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale
open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig
open CategoryTheory.Functor.RightDerived
open RingedSite.Hom.ModuleSections.Underlying
open RingedSite.Hom RingedSite.Cocontinuous

universe u

/- Lemma 84.5.4 (1): ordinary derived cohomology on the big étale site over `X` agrees with
the cohomology of the identity inverse image on the small étale site. -/
@[stacks 0DGB] #check (AlgebraicGeometry.AlgebraicSpace.Etale.Derived.etaleCohomology_piInverseImage :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) (n : ℤ)
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
    (K : DerivedCategory (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})),
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((siteAbelianSectionsDerived (overEtaleTopology X) (Over.mk (𝟙 X))).obj
          ((etalePiInverseImage X).mapDerivedCategory.obj K)))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((Cochain.functor (globalSections X)).obj K)))

/- Lemma 84.5.4 (2): module-valued derived cohomology on the big étale site agrees with the
cohomology of the identity pullback on the small étale site. -/
@[stacks 0DGB] #check (AlgebraicGeometry.AlgebraicSpace.Etale.Derived.etaleModuleCohomology_piPullback :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) (n : ℤ)
    [UnivLE.{u + 1, u + 1}]
    [HasWeakSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasGlobalSectionsFunctor (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1} (ringedSite X))]
    [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1} (Big.ringedSite X))]
    [(etalePiModulePushforward X).IsRightAdjoint]
    [Functor.HasLeftDerivedFunctor
      (etalePiModuleToDerived X)
      (ModuleQis.{u + 1} (ringedSite X))]
    (K : ModuleDerived.{u + 1} (ringedSite X)),
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((sectionsDerived.{u + 1} (Big.ringedSite X) (Over.mk (𝟙 X))).obj
          ((etalePiModulePullbackDerived X).obj K)))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((moduleGlobalSectionsDerived.{u + 1} (ringedSite X)).obj K)))

/- Lemma 84.5.4 (3): ordinary derived cohomology on `Y` agrees with small-site cohomology after
the inverse image associated to `f : Y ⟶ X`. -/
@[stacks 0DGB] #check (AlgebraicGeometry.AlgebraicSpace.Etale.Derived.etaleCohomology_smallInverseImage :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X) (n : ℤ)
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
    (K : DerivedCategory (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})),
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((siteAbelianSectionsDerived (overEtaleTopology X) (Over.mk f)).obj
          ((etalePiInverseImage X).mapDerivedCategory.obj K)))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((Cochain.functor (globalSections Y)).obj
          ((sheafInverseImage AddCommGrpCat.{u + 1} f).mapDerivedCategory.obj K))))

/- Lemma 84.5.4 (4): module-valued derived cohomology on `Y` agrees with small-site cohomology
after the derived pullback associated to `f : Y ⟶ X`. -/
@[stacks 0DGB] #check (AlgebraicGeometry.AlgebraicSpace.Etale.Derived.etaleModuleCohomology_smallPullback :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X) (n : ℤ)
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
    (K : ModuleDerived.{u + 1} (ringedSite X)),
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((sectionsDerived.{u + 1} (Big.ringedSite X) (Over.mk f)).obj
          ((etalePiModulePullbackDerived X).obj K)))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((moduleGlobalSectionsDerived.{u + 1} (ringedSite Y)).obj
          ((etaleSmallModulePullbackDerived f).obj K))))

/- Lemma 84.5.4 (5): ordinary derived cohomology on the big site over `X` agrees with cohomology
on the small étale site of `Y` after relocalization. -/
@[stacks 0DGB] #check (AlgebraicGeometry.AlgebraicSpace.Etale.Derived.etaleCohomology_relocalization :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X) (n : ℤ)
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [HasSheafify (overEtaleTopology X) AddCommGrpCat.{u + 1}]
    [IsGrothendieckAbelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
    [IsGrothendieckAbelian (Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Functor.HasRightDerivedFunctor
      (Cochain.toDerived (globalSections Y))
      (HomologicalComplex.quasiIso
        (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) (ComplexShape.up ℤ))]
    (M : DerivedCategory (Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1})),
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((siteAbelianSectionsDerived (overEtaleTopology X) (Over.mk f)).obj M))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((Cochain.functor (globalSections Y)).obj
          ((siteAbelianInverseImageDerived (smallEtaleTopology Y)
            (overEtaleTopology X) (relocalizationFunctor f)).obj M))))

/- Lemma 84.5.4 (6): module-valued derived cohomology on the big site over `X` agrees with
cohomology on the small étale site of `Y` after relocalization. -/
@[stacks 0DGB] #check (AlgebraicGeometry.AlgebraicSpace.Etale.Derived.etaleModuleCohomology_relocalization :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X) (n : ℤ)
    [UnivLE.{u + 1, u + 1}]
    [HasWeakSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [HasGlobalSectionsFunctor (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1} (ringedSite Y))]
    [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1} (Big.ringedSite X))]
    (M : ModuleDerived.{u + 1} (Big.ringedSite X)),
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((sectionsDerived.{u + 1} (Big.ringedSite X) (Over.mk f)).obj M))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((moduleGlobalSectionsDerived.{u + 1} (ringedSite Y)).obj
          ((relocalizationModuleDerived f).obj M))))

