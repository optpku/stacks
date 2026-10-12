/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived.Underlying
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Cochain
public import ReasLib.CategoryTheory.Sites.Derived.InverseImage
public import ReasLib.CategoryTheory.Sites.Derived.Sections
public import ReasLib.CategoryTheory.Sites.MorphismOfSites
public import stacks_project.Chap66.Lemma_66_18_12_Pushforward
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap69.Lemma_69_6_3_DerivedSections
public import stacks_project.Chap84.Lemma_84_5_2_Relocalization
public import stacks_project.Chap84.Lemma_84_5_4_Ringed
public import stacks_project.Chap84.Lemma_84_5_5_SmallToBig

/-!
# Derived comparison of big and small étale cohomology of algebraic spaces

Étale cohomology on `(Spaces/X)_étale` agrees with small-site cohomology after
`π_X⁻¹`, `Lπ_X^*`, `f_small⁻¹`, `Lf_small^*`, `i_f⁻¹`, and `i_f^*`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Etale.SmallToBig
open RingedSite.Hom
open RingedSite.Hom.ModuleSections.Underlying
open RingedSite.Cocontinuous
open CategoryTheory.Functor.RightDerived

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Etale

variable {S : Scheme.{u}}

namespace Derived

variable {S : Scheme.{u}}

/-- Pullback from the small étale site to the big étale site identifies derived cohomology with
small-site cohomology of `X`. -/
theorem etaleCohomology_piInverseImage {X Y : AlgebraicSpace S} (f : Y ⟶ X) (n : ℤ)
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (overEtaleTopology X) AddCommGrpCat.{u + 1}]
    [IsGrothendieckAbelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [IsGrothendieckAbelian (Sheaf (overEtaleTopology X) AddCommGrpCat.{u + 1})]
    [∀ P : (smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (relocalizationFunctor (𝟙 X)).op.HasLeftKanExtension P]
    [PreservesFiniteLimits
      ((relocalizationFunctor (𝟙 X)).op.lan :
        ((smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤
          ((Over X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}))]
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

/-- Identity-base derived module pullback identifies big and small étale cohomology. -/
theorem etaleModuleCohomology_piPullback {X Y : AlgebraicSpace S} (f : Y ⟶ X) (n : ℤ)
    [UnivLE.{u + 1, u + 1}]
    [HasWeakSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasGlobalSectionsFunctor (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1} (ringedSite X))]
    [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1} (overEtaleRingedSite X))]
    [(etalePiRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint]
    [Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{u + 1} (etalePiRingedHom X))
      (ModuleQis.{u + 1} (ringedSite X))]
    (K : ModuleDerived.{u + 1} (ringedSite X)) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((sectionsDerived.{u + 1} (overEtaleRingedSite X) (Over.mk (𝟙 X))).obj
          ((modulePullbackDerived.{u + 1} (etalePiRingedHom X)).obj K)))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((moduleGlobalSectionsDerived.{u + 1} (ringedSite X)).obj K)) :=
  sorry

/-- The derived inverse image along a morphism of algebraic spaces identifies the corresponding
big and small étale cohomology groups. -/
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
    [PreservesFiniteLimits
      ((relocalizationFunctor (𝟙 X)).op.lan :
        ((smallEtaleSite X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤
          ((Over X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}))]
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

/-- Derived module pullback along a morphism of algebraic spaces identifies big and small
étale cohomology. -/
theorem etaleModuleCohomology_smallPullback {X Y : AlgebraicSpace S} (f : Y ⟶ X) (n : ℤ)
    [UnivLE.{u + 1, u + 1}]
    [HasWeakSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [HasGlobalSectionsFunctor (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1} (ringedSite X))]
    [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1} (overEtaleRingedSite X))]
    [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1} (ringedSite Y))]
    [(etalePiRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint]
    [Functor.HasLeftDerivedFunctor
      (modulePullbackToDerived.{u + 1} (etalePiRingedHom X))
      (ModuleQis.{u + 1} (ringedSite X))]
    (K : ModuleDerived.{u + 1} (ringedSite X)) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((sectionsDerived.{u + 1} (overEtaleRingedSite X) (Over.mk f)).obj
          ((modulePullbackDerived.{u + 1} (etalePiRingedHom X)).obj K)))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((moduleGlobalSectionsDerived.{u + 1} (ringedSite Y)).obj
          ((etaleSmallModulePullbackDerived f).obj K))) :=
  sorry

/-- Relocalization from the big étale site to the small étale site identifies derived
cohomology. -/
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

/-- Relocalization identifies derived module cohomology on the big and small étale sites. -/
theorem etaleModuleCohomology_relocalization {X Y : AlgebraicSpace S} (f : Y ⟶ X) (n : ℤ)
    [UnivLE.{u + 1, u + 1}]
    [HasWeakSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [HasGlobalSectionsFunctor (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1} (ringedSite Y))]
    [IsGrothendieckAbelian (RingedSite.ModuleCat.{u + 1} (overEtaleRingedSite X))]
    (M : ModuleDerived.{u + 1} (overEtaleRingedSite X)) :
    IsIsomorphic
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((sectionsDerived.{u + 1} (overEtaleRingedSite X) (Over.mk f)).obj M))
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n).obj
        ((moduleGlobalSectionsDerived.{u + 1} (ringedSite Y)).obj
          ((relocalizationModuleDerived f).obj M))) :=
  sorry

end Derived

end AlgebraicGeometry.AlgebraicSpace.Etale
