/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Flat.Generators
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Flat
public import ReasLib.Topology.Opens.Instances

/-!
# Flat localized generators for module sheaves on ringed spaces

The generic ringed-site generators specialize to the opens site of a ringed space. This leaf owns
the short geometric names used by resolutions and derived constructions.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Modules

variable {X : RingedSpace.{u}}

/-- Restriction of module sheaves to every slice of the opens site has its canonical right
adjoint. Bundling the pointwise instances as a dependent instance lets localized-generator APIs
infer the whole family without local `letI` declarations. -/
noncomputable instance localizedRestrictionIsRightAdjoint (X : RingedSpace.{u}) :
    ∀ U : Opens X,
      (SheafOfModules.Localization.restriction (RingedSpace.ringCatSheaf X) U).IsRightAdjoint :=
  sorry

/-- In the universe of `X.Modules`, use the constructed sheafification adjunction.
The higher priority keeps localized-generator data independent of the admitted,
universe-polymorphic adjoint-existence instance above. -/
noncomputable instance (priority := 1100) localizedRestrictionIsRightAdjointForModules
    (X : RingedSpace.{u}) :
    ∀ U : Opens X,
      (SheafOfModules.Localization.restriction (RingedSpace.ringCatSheaf X) U :
        X.Modules ⥤ SheafOfModules.{u} ((RingedSpace.ringCatSheaf X).over U)).IsRightAdjoint :=
  fun U ↦ SheafOfModules.Localization.restrictionIsRightAdjoint
    (RingedSpace.ringCatSheaf X) U

/-- The structure module on `U`, extended to `X` by lower shriek. -/
@[stacks 05NH "ringed-space generator", stacks 05NI "generator"]
noncomputable abbrev localizedGenerator (X : RingedSpace.{u}) (U : Opens X) : X.Modules :=
  SheafOfModules.RingedSite.localizedStructureModuleExtensionByZero X.sheaf U

/-- The localized structure-module generator is flat as a module sheaf on the ringed space. -/
@[stacks 05NH "ringed-space generator flatness", instance]
theorem localizedGenerator_isFlat (X : RingedSpace.{u}) (U : Opens X) :
    (localizedGenerator X U).IsFlat := sorry

/-- Module sheaves which are coproducts of localized structure-module generators. -/
@[stacks 05NI "ringed-space specialization"]
abbrev localizedGeneratorCoproducts (X : RingedSpace.{u}) :
    ObjectProperty X.Modules :=
  SheafOfModules.RingedSite.localizedGeneratorCoproducts X.sheaf

/-- A localized generator maps to a module sheaf by specifying its universal section. -/
noncomputable def localizedGeneratorSectionMap (ℱ : X.Modules) (U : Opens X)
    (s : ℱ.val.obj (Opposite.op U)) : localizedGenerator X U ⟶ ℱ :=
  (SheafOfModules.Localization.structureModuleHomEquiv
    (RingedSpace.ringCatSheaf X) U ℱ).symm s

/-- The generator map represents the prescribed section. -/
@[simp]
theorem localizedGeneratorSectionMap_spec (ℱ : X.Modules) (U : Opens X)
    (s : ℱ.val.obj (Opposite.op U)) :
    SheafOfModules.Localization.structureModuleHomEquiv
      (RingedSpace.ringCatSheaf X) U ℱ (localizedGeneratorSectionMap ℱ U s) = s :=
  Equiv.apply_symm_apply _ s

/-- The canonical flat cover is indexed by all local sections `(U, s)`. -/
noncomputable def sectionFlatCover (ℱ : X.Modules) : X.Modules :=
  ∐ fun p : Σ U : Opens X, ℱ.val.obj (Opposite.op U) ↦ localizedGenerator X p.1

/-- The cover map sends the universal section of the `(U, s)` summand to `s`. -/
noncomputable def sectionFlatCoverπ (ℱ : X.Modules) : sectionFlatCover ℱ ⟶ ℱ :=
  Sigma.desc fun p ↦ localizedGeneratorSectionMap ℱ p.1 p.2

/-- The component of the canonical cover map at a local section is its representing map. -/
@[reassoc (attr := simp)]
theorem sectionFlatCover_ι_π (ℱ : X.Modules)
    (p : Σ U : Opens X, ℱ.val.obj (Opposite.op U)) :
    Sigma.ι (fun p : Σ U : Opens X, ℱ.val.obj (Opposite.op U) ↦
      localizedGenerator X p.1) p ≫ sectionFlatCoverπ ℱ =
        localizedGeneratorSectionMap ℱ p.1 p.2 := by
  apply Sigma.ι_desc

/-- A coproduct of the flat localized generators is flat. -/
@[stacks 05NG "canonical section cover", instance]
theorem sectionFlatCover_isFlat (ℱ : X.Modules) : (sectionFlatCover ℱ).IsFlat := sorry

/-- Every local section is represented by its own summand, so the cover map is epic. -/
@[stacks 05NI "canonical section cover", instance]
theorem sectionFlatCoverπ_epi (ℱ : X.Modules) : Epi (sectionFlatCoverπ ℱ) := sorry

/-- Every module sheaf on a ringed space is an epimorphic image of a
coproduct of localized structure-module generators. -/
@[stacks 05NI "(1)"]
theorem exists_epi_from_localizedGenerators (ℱ : X.Modules) :
    ∃ (I : Type u) (U : I → Opens X)
      (φ : (∐ fun i ↦ localizedGenerator X (U i)) ⟶ ℱ), Epi φ := by
  exact ⟨(Σ U : Opens X, ℱ.val.obj (Opposite.op U)), Sigma.fst,
    sectionFlatCoverπ ℱ, sectionFlatCoverπ_epi ℱ⟩

/-- Every module sheaf on a ringed space is an epimorphic image of a
flat module sheaf. -/
@[stacks 05NI "(2)"]
theorem exists_epi_from_flat (ℱ : X.Modules) :
    ∃ (𝒢 : X.Modules) (_ : 𝒢.IsFlat) (φ : 𝒢 ⟶ ℱ), Epi φ :=
  ⟨sectionFlatCover ℱ, sectionFlatCover_isFlat ℱ,
    sectionFlatCoverπ ℱ, sectionFlatCoverπ_epi ℱ⟩

end AlgebraicGeometry.RingedSpace.Modules
