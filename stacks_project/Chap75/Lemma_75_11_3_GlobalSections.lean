module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived
public import stacks_project.Chap69.Lemma_69_16_2_Tensor
public import stacks_project.Chap75.Lemma_75_11_2_Coherator

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.GlobalSections

/-! # Compatibility checks for module-valued derived global sections -/

@[expose] public section

open AlgebraicGeometry CategoryTheory ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.moduleGlobalSectionsFunctor :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    X.Modules ⥤ ModuleCat.{u} (globalSectionsRing X))

#check (AlgebraicGeometry.AlgebraicSpace.moduleGlobalSectionsFunctor_obj :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) (F : X.Modules),
    (moduleGlobalSectionsFunctor X).obj F = moduleGlobalSections X F)

#check (AlgebraicGeometry.AlgebraicSpace.moduleGlobalSectionsFunctor.additive :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S), (moduleGlobalSectionsFunctor X).Additive)

#check (AlgebraicGeometry.AlgebraicSpace.instHasDerivedCategory_globalSectionsModuleCat :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    HasDerivedCategory (ModuleCat.{u} (globalSectionsRing X)))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.moduleDerivedGlobalSections :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    ModuleDerived X ⥤ DerivedCategory (ModuleCat.{u} (globalSectionsRing X)))

#check (AlgebraicGeometry.AlgebraicSpace.Modules.moduleDerivedGlobalSections.unit :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    (moduleGlobalSectionsFunctor X).mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q :
          CochainComplex (ModuleCat.{u} (globalSectionsRing X)) ℤ ⥤
            DerivedCategory (ModuleCat.{u} (globalSectionsRing X))) ⟶
      (DerivedCategory.Q : CochainComplex (Modules X) ℤ ⥤ DerivedCategory (Modules X)) ⋙
        Modules.moduleDerivedGlobalSections X)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.moduleDerivedGlobalSections.isRightDerived :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    (Modules.moduleDerivedGlobalSections X).IsRightDerivedFunctor
      (Modules.moduleDerivedGlobalSections.unit X)
      (HomologicalComplex.quasiIso (Modules X) (up ℤ)))

end AlgebraicGeometry.AlgebraicSpace
