/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived
public import stacks_project.Chap69.Lemma_69_16_2_Tensor
public import stacks_project.Chap75.Lemma_75_11_2_Coherator

/-!
# Global sections of modules on algebraic spaces as A-modules

The underived functor `Γ(X, -)` lands in modules over `A = Γ(X, 𝒪_X)`, and its
K-injective right-derived functor is `RΓ(X, -) : D(𝒪_X) ⥤ D(A)`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The functor sending an `𝒪_X`-module to its global sections as a module over
`A = Γ(X, 𝒪_X)`. -/
noncomputable def moduleGlobalSectionsFunctor {S : Scheme.{u}} (X : AlgebraicSpace S) :
    X.Modules ⥤ ModuleCat.{u} (globalSectionsRing X) :=
  toSpecAPushforward X ⋙ moduleSpecΓFunctor (R := globalSectionsRing X)

/-- On objects, `moduleGlobalSectionsFunctor` recovers `moduleGlobalSections`. -/
theorem moduleGlobalSectionsFunctor_obj {S : Scheme.{u}} (X : AlgebraicSpace S)
    (F : X.Modules) :
    (moduleGlobalSectionsFunctor X).obj F = moduleGlobalSections X F :=
  sorry

/-- Global sections as an `A`-module is an additive functor. -/
instance moduleGlobalSectionsFunctor.additive {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (moduleGlobalSectionsFunctor X).Additive :=
  sorry

/-- The standard derived-category structure on modules over `Γ(X, 𝒪_X)`. -/
instance instHasDerivedCategory_globalSectionsModuleCat {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    HasDerivedCategory (ModuleCat.{u} (globalSectionsRing X)) :=
  HasDerivedCategory.standard (ModuleCat.{u} (globalSectionsRing X))

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The unbounded derived global-sections functor `RΓ(X, -) : D(𝒪_X) ⥤ D(A)`. -/
noncomputable abbrev moduleDerivedGlobalSections {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ModuleDerived X ⥤ DerivedCategory (ModuleCat.{u} (globalSectionsRing X)) :=
  Functor.RightDerived.KInjective.functor.{u} (moduleGlobalSectionsFunctor X)

namespace moduleDerivedGlobalSections

/-- The cochain-level comparison unit for derived global sections. -/
noncomputable abbrev unit {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (moduleGlobalSectionsFunctor X).mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q :
          CochainComplex (ModuleCat.{u} (globalSectionsRing X)) ℤ ⥤
            DerivedCategory (ModuleCat.{u} (globalSectionsRing X))) ⟶
      (DerivedCategory.Q : CochainComplex (Modules X) ℤ ⥤ DerivedCategory (Modules X)) ⋙
        moduleDerivedGlobalSections X :=
  Functor.RightDerived.KInjective.unit.{u} (moduleGlobalSectionsFunctor X)

/-- Derived global sections satisfies the universal property of a right-derived functor. -/
instance isRightDerived {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (moduleDerivedGlobalSections X).IsRightDerivedFunctor (unit X)
      (HomologicalComplex.quasiIso (Modules X) (up ℤ)) :=
  Functor.RightDerived.KInjective.isRightDerived (moduleGlobalSectionsFunctor X)

end moduleDerivedGlobalSections

end AlgebraicGeometry.AlgebraicSpace.Modules
