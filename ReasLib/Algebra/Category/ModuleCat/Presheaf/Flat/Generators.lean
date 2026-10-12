/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Flat.Colimits
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Flat.Localization
public import ReasLib.CategoryTheory.ObjectProperty.Cover
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat generators for module presheaves and sheaves

This leaf separates two useful abstraction levels.  `EnoughFlatObjects` is the compact interface
used by homological algebra.  The more concrete theorems exhibit coproducts of localized
structure modules when the corresponding lower-shriek infrastructure is available.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ObjectProperty

noncomputable section

universe u v

namespace PresheafOfModules

section FlatCovers

variable {C : Type u} [Category.{v} C]
variable {𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}}

/-- Every module presheaf is an epimorphic image of a flat module presheaf. -/
@[stacks 03EW "presheaf flat cover"]
theorem exists_epi_from_flat
    (ℱ : PresheafOfModules (ringPresheaf 𝒪)) :
    ∃ (𝒢 : PresheafOfModules (ringPresheaf 𝒪)) (_ : IsFlat 𝒢)
      (φ : 𝒢 ⟶ ℱ), Epi φ := sorry

/-- Module presheaves have enough flat objects. -/
instance enoughFlatObjects :
    CategoryTheory.MonoidalCategory.EnoughFlatObjects
      (PresheafOfModules (ringPresheaf 𝒪)) := sorry

end FlatCovers

section LocalizedGenerators

variable {C : Type u} [Category.{u} C]
variable {𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- Every module presheaf is an epimorphic image of a coproduct of localized structure
modules. -/
@[stacks 03EW "presheaf localized generators"]
theorem exists_epi_from_coproduct_structureModule
    (ℱ : PresheafOfModules (ringPresheaf 𝒪)) :
    ∃ (I : Type u) (U : I → C)
      (φ : (∐ fun i ↦ Localization.structureModule 𝒪 (U i)) ⟶ ℱ), Epi φ := sorry

end LocalizedGenerators

end PresheafOfModules

namespace SheafOfModules.RingedSite

section FlatCovers

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

/-- Every module sheaf is an epimorphic image of a flat module sheaf. -/
@[stacks 03EW "sheaf flat cover"]
theorem exists_epi_from_flat
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    ∃ (𝒢 : ringedSiteModuleCategory J 𝒪) (_ : IsFlat 𝒪 𝒢)
      (φ : 𝒢 ⟶ ℱ), Epi φ := sorry

/-- Module sheaves on a ringed site have enough flat objects. -/
instance enoughFlatObjects :
    CategoryTheory.MonoidalCategory.EnoughFlatObjects
      (ringedSiteModuleCategory J 𝒪) := sorry

end FlatCovers

section LocalizedGenerators

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [∀ U : C,
  (SheafOfModules.Localization.restriction (ringSheaf J 𝒪) U).IsRightAdjoint]

/-- Every module sheaf is an epimorphic image of a coproduct of localized structure modules. -/
@[stacks 03EW "sheaf localized generators"]
theorem exists_epi_from_coproduct_structureModule
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    ∃ (I : Type (max u v)) (U : I → C)
      (φ : (∐ fun i ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)) ⟶ ℱ), Epi φ := sorry

/-- 21.42.2.1 (08S1): every module sheaf occurs as the cokernel term of the canonical
kernel sequence of an epimorphism from a coproduct of localized structure modules. -/
@[stacks 08S1]
theorem exists_shortExact_coproduct_structureModule
    (ℱ : ringedSiteModuleCategory J 𝒪) :
    ∃ (I : Type (max u v)) (U : I → C)
      (φ : (∐ fun i ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)) ⟶ ℱ),
      (ShortComplex.kernelSequence φ).ShortExact := sorry

/-- The object property of being a coproduct of localized structure modules `j![𝒪, U]`. -/
@[stacks 05NI "localized generator coproducts"]
def localizedGeneratorCoproducts
    (𝒪 : Sheaf J CommRingCat.{max u v})
    [∀ U : C, (SheafOfModules.Localization.restriction (ringSheaf J 𝒪) U).IsRightAdjoint] :
    ObjectProperty (ringedSiteModuleCategory J 𝒪) :=
  fun ℱ ↦ ∃ (I : Type (max u v)) (U : I → C),
    Nonempty (ℱ ≅ ∐ fun i ↦ localizedStructureModuleExtensionByZero 𝒪 (U i))

/-- Coproducts of localized structure modules are stable under ambient isomorphisms. -/
instance localizedGeneratorCoproducts_isClosedUnderIsomorphisms
    (𝒪 : Sheaf J CommRingCat.{max u v})
    [∀ U : C, (SheafOfModules.Localization.restriction (ringSheaf J 𝒪) U).IsRightAdjoint] :
    (localizedGeneratorCoproducts 𝒪).IsClosedUnderIsomorphisms := sorry

/-- The zero module is the empty coproduct of localized structure modules. -/
instance localizedGeneratorCoproducts_containsZero
    (𝒪 : Sheaf J CommRingCat.{max u v})
    [∀ U : C, (SheafOfModules.Localization.restriction (ringSheaf J 𝒪) U).IsRightAdjoint] :
    (localizedGeneratorCoproducts 𝒪).ContainsZero := sorry

/-- Coproducts of localized structure modules are closed under finite coproducts. -/
instance localizedGeneratorCoproducts_isClosedUnderFiniteCoproducts
    (𝒪 : Sheaf J CommRingCat.{max u v})
    [∀ U : C, (SheafOfModules.Localization.restriction (ringSheaf J 𝒪) U).IsRightAdjoint] :
    (localizedGeneratorCoproducts 𝒪).IsClosedUnderFiniteCoproducts := sorry

/-- Every module sheaf admits an epimorphic cover by a coproduct of localized structure
modules. -/
instance localizedGeneratorCoproducts_hasEpiCover
    (𝒪 : Sheaf J CommRingCat.{max u v})
    [∀ U : C, (SheafOfModules.Localization.restriction (ringSheaf J 𝒪) U).IsRightAdjoint] :
    ObjectProperty.HasEpiCover (localizedGeneratorCoproducts 𝒪) := sorry

end LocalizedGenerators

end SheafOfModules.RingedSite
