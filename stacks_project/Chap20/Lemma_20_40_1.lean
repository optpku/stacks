/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections
public import stacks_project.Chap20.«20_40_0_1»
public import ReasLib.Topology.Opens.Instances

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open ComplexShape
open AlgebraicGeometry.RingedSpace.Module.Derived.GlobalSections

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}} {ι : Type u} [Finite ι]

/-- The total alternating Čech complex of a complex of `𝒪_X`-modules, formed after
forgetting to abelian sheaves on the underlying space. -/
@[stacks 08C1 "module alternating Cech total complex"]
abbrev moduleAlternatingCechTotalComplexFunctor (X : RingedSpace.{u})
    (𝒰 : ι → Opens X.carrier) :
    CochainComplex (RingedSpace.Modules X) ℤ ⥤ CochainComplex AddCommGrpCat.{u} ℤ :=
  (SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    TopCat.Sheaf.alternatingCechTotalComplexFunctor X.carrier 𝒰

/-- The total alternating Čech complex of a complex of `𝒪_X`-modules, viewed in
`D(AddCommGrpCat)`. -/
@[stacks 08C1 "module alternating Cech complex in the derived category"]
abbrev moduleAlternatingCechToDerivedFunctor (X : RingedSpace.{u})
    (𝒰 : ι → Opens X.carrier) :
    CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory AddCommGrpCat.{u} :=
  moduleAlternatingCechTotalComplexFunctor X 𝒰 ⋙ DerivedCategory.Q

/-- The module-level comparison of `20.40.0.1`, after forgetting to abelian sheaves, is the
transport of the sheaf-level comparison across the canonical global-sections identification. -/
@[stacks 08C1 "module global-sections to alternating Cech comparison"]
def IsModuleGlobalSectionsToAlternatingCechTotalMap (X : RingedSpace.{u})
    (𝒰 : ι → Opens X.carrier) (K : CochainComplex (RingedSpace.Modules X) ℤ)
    (α :
      (((moduleGlobalSectionsFunctor X ⋙
          forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) ⟶
        (moduleAlternatingCechTotalComplexFunctor X 𝒰).obj K) : Prop :=
  let L :=
    ((SheafOfModules.toSheaf (RingedSpace.ringCatSheaf X)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K
  ∃ β : TopCat.Sheaf.globalSectionsComplex X.carrier L ⟶
      (TopCat.Sheaf.alternatingCechTotalComplexFunctor X.carrier 𝒰).obj L,
    TopCat.Sheaf.IsGlobalSectionsToAlternatingCechTotalMap X.carrier 𝒰 L β ∧
      α = (additiveComplexIso X).hom.app K ≫ β

omit [Finite ι] in
/-- The comparison of `20.40.0.1` for complexes of `𝒪_X`-modules is unique after
transporting the sheaf-level comparison across the canonical source identification. -/
@[stacks 08C1 "uniqueness of the module alternating Cech comparison"]
theorem existsUnique_moduleGlobalSectionsToAlternatingCechTotalMap
    (X : RingedSpace.{u}) (𝒰 : ι → Opens X.carrier)
    (K : CochainComplex (RingedSpace.Modules X) ℤ) :
    ∃! α :
      (((moduleGlobalSectionsFunctor X ⋙
          forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) ⟶
        (moduleAlternatingCechTotalComplexFunctor X 𝒰).obj K,
      IsModuleGlobalSectionsToAlternatingCechTotalMap X 𝒰 K α := sorry

/-- A comparison from the total alternating Čech complex to abelian-valued derived global
sections has the expected source-facing compatibility if, for every complex `K`, it identifies
after precomposition with the canonical transported map from abelian global sections of `K`. -/
@[stacks 08C1 "compatibility of an alternating Cech derived comparison"]
def IsModuleAlternatingCechToDerivedGlobalSectionsComparison (X : RingedSpace.{u})
    (𝒰 : ι → Opens X.carrier)
    (τ :
      moduleAlternatingCechToDerivedFunctor X 𝒰 ⟶
        (DerivedCategory.Q :
          CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory (RingedSpace.Modules X)) ⋙
          toAbelian X) : Prop :=
  ∀ K : CochainComplex (RingedSpace.Modules X) ℤ,
    ∃ α :
      (((moduleGlobalSectionsFunctor X ⋙
          forget₂ (ModuleCat (globalSectionsRing X)) AddCommGrpCat.{u}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K) ⟶
        (moduleAlternatingCechTotalComplexFunctor X 𝒰).obj K,
      IsModuleGlobalSectionsToAlternatingCechTotalMap X 𝒰 K α ∧
        DerivedCategory.Q.map α ≫ τ.app K =
          cochainToAbelianUnitApp X K

-- Proof sketch: choose a functorial K-injective resolution of complexes of `𝒪_X`-
-- modules. Apply `20.40.0.1` to the chosen K-injective resolution, use the finite-cover
-- acyclicity of injective terms to see that this Čech map computes derived global sections, and
-- descend the resulting comparison along the quasi-isomorphism from the original complex to its
-- resolution. Naturality comes from functoriality of the chosen resolution, and compatibility says
-- that precomposing with the localized map of `20.40.0.1` recovers the canonical derived-unit map
-- for abelian global sections.
/-- Lemma 20.40.1: for a finite open covering `𝒰` with `iSup 𝒰 = ⊤` of a ringed space
`(X, 𝒪_X)`, there exists a functorial comparison from the total alternating Čech complex
of a complex of `𝒪_X`-modules to `RΓ(X, -)` in `D(AddCommGrpCat)`, and this
comparison is compatible with the canonical map of `20.40.0.1` from the underived global-sections
complex to the total alternating Čech complex. -/
@[stacks 08C1]
theorem exists_moduleAlternatingCechToDerivedGlobalSections
    (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = ⊤) :
    ∃ τ :
      moduleAlternatingCechToDerivedFunctor X 𝒰 ⟶
        (DerivedCategory.Q : CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory (RingedSpace.Modules X)) ⋙
          toAbelian X,
      IsModuleAlternatingCechToDerivedGlobalSectionsComparison X 𝒰 τ := sorry

end AlgebraicGeometry.RingedSpace
