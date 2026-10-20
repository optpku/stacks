module

public import ReasLib.Algebra.Homology.DerivedCategory.AddCommGrpCat
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Additive
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.Tactic.CrossRefAttribute

/-!
# Global cohomology of module sheaves on ringed sites

Module-valued global cohomology is `Ext` from the structure sheaf, regarded as the unit module.
This file exposes the functor, its value, and its action on morphisms so later constructions can
use one canonical owner instead of repeating the `Ext` expression.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian

noncomputable section

universe u v w

namespace RingedSite.Hom

variable (X : RingedSite.{u, v, w}) [Abelian (ModuleCat.{w} X)]
variable [HasExt (ModuleCat.{w} X)]

/-- Degree-`p` global cohomology as a functor on `𝒪_X`-modules. -/
@[stacks 03FD "module global-cohomology functor"]
abbrev moduleGlobalCohomologyFunctor (p : ℕ) :
    ModuleCat.{w} X ⥤ AddCommGrpCat.{w} :=
  Abelian.extFunctorObj (SheafOfModules.unit X.structureSheaf) p

/-- Degree-`p` global cohomology of an `𝒪_X`-module. -/
@[stacks 03FD "module global cohomology"]
abbrev moduleGlobalCohomology (ℱ : ModuleCat.{w} X) (p : ℕ) :
    AddCommGrpCat.{w} :=
  (moduleGlobalCohomologyFunctor (X := X) p).obj ℱ

/-- The map on module global cohomology induced by a module morphism. -/
@[stacks 03FD "module global-cohomology naturality"]
abbrev moduleGlobalCohomologyMap {ℱ 𝒢 : ModuleCat.{w} X}
    (φ : ℱ ⟶ 𝒢) (p : ℕ) :
    moduleGlobalCohomology (X := X) ℱ p ⟶
      moduleGlobalCohomology (X := X) 𝒢 p :=
  (moduleGlobalCohomologyFunctor (X := X) p).map φ

variable [HasWeakSheafify X.siteTopology AddCommGrpCat.{w}]
variable [HasGlobalSectionsFunctor X.siteTopology AddCommGrpCat.{w}]
variable [HasInjectiveResolutions (ModuleCat.{w} X)]

/-- A chosen injective resolution computes module global cohomology by applying additive global
sections and taking homology. -/
@[stacks 071H "module cohomology from an injective resolution"]
theorem moduleGlobalCohomology_isomorphic_homology_of_injectiveResolution
    (ℱ : ModuleCat.{w} X) (I : InjectiveResolution ℱ) (p : ℕ) :
    IsIsomorphic (moduleGlobalCohomology (X := X) ℱ p)
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{w}
        (ComplexShape.up ℕ) p).obj
          (((moduleGlobalSectionsAdditiveFunctor.{w} X).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj I.cocomplex)) := sorry

end RingedSite.Hom
