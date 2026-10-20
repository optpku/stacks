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

/-- Every module sheaf on a ringed space is an epimorphic image of a
coproduct of localized structure-module generators. -/
@[stacks 05NI "(1)"]
theorem exists_epi_from_localizedGenerators (ℱ : X.Modules) :
    ∃ (I : Type u) (U : I → Opens X)
      (φ : (∐ fun i ↦ localizedGenerator X (U i)) ⟶ ℱ), Epi φ := sorry

/-- Every module sheaf on a ringed space is an epimorphic image of a
flat module sheaf. -/
@[stacks 05NI "(2)"]
theorem exists_epi_from_flat (ℱ : X.Modules) :
    ∃ (𝒢 : X.Modules) (_ : 𝒢.IsFlat) (φ : 𝒢 ⟶ ℱ), Epi φ := sorry

end AlgebraicGeometry.RingedSpace.Modules
