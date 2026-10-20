/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Invertible
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.NonvanishingLocus

/-!
# Nonvanishing Opens of Sections of Invertible Module Sheaves

This file upgrades the stalkwise nonvanishing locus of a section to its canonical open subset
and records the induced trivialization over that open.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open Opposite
open TopologicalSpace
open SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable (X : RingedSpace.{u})

/-- The morphism from the structure module induced by restricting a global section to `U`. -/
@[stacks 01CY "restricted section morphism"]
noncomputable abbrev sectionOverHom (ℒ : X.Modules) (s : ℒ.sections) (U : Opens X) :
    SheafOfModules.unit (X.ringCatSheaf.over U) ⟶ ℒ.over U :=
  (ℒ.over U).unitHomEquiv.symm
    (SheafOfModules.pushforwardSections (𝟙 (X.ringCatSheaf.over U)) s)

section Nonvanishing

variable [∀ x : X, IsLocalRing (X.presheaf.stalk x)]

/-- For an invertible module sheaf, the stalkwise nonvanishing locus of a global section is
open. -/
@[stacks 01CY "openness"]
theorem sectionNonvanishingLocus_isOpen (ℒ : X.Modules)
    [MonoidalCategory.isInvertibleObject ℒ]
    (s : ℒ.sections) :
    IsOpen (sectionNonvanishingLocus X ℒ s) := sorry

/-- The open subset cut out by the nonvanishing locus of a global section of an invertible module
sheaf. Its carrier is the stalkwise locus `sectionNonvanishingLocus X ℒ s`. -/
@[stacks 01CY "nonvanishing open"]
def sectionNonvanishingOpen (ℒ : X.Modules)
    [MonoidalCategory.isInvertibleObject ℒ]
    (s : ℒ.sections) : Opens X :=
  ⟨sectionNonvanishingLocus X ℒ s, sectionNonvanishingLocus_isOpen X ℒ s⟩

/-- The carrier of `sectionNonvanishingOpen` is the stalkwise nonvanishing locus used to define
it. -/
@[simp]
theorem coe_sectionNonvanishingOpen (ℒ : X.Modules)
    [MonoidalCategory.isInvertibleObject ℒ]
    (s : ℒ.sections) :
    (sectionNonvanishingOpen X ℒ s : Set X) = sectionNonvanishingLocus X ℒ s := sorry

/-- On the nonvanishing open of a global section of an invertible module sheaf, the restricted
section induces an isomorphism from the structure module. -/
@[stacks 01CY "trivialization"]
instance isIso_restrictedSection_sectionNonvanishingOpen (ℒ : X.Modules)
    [MonoidalCategory.isInvertibleObject ℒ]
    (s : ℒ.sections) :
    IsIso (sectionOverHom X ℒ s (sectionNonvanishingOpen X ℒ s)) := sorry

/-- The restricted nonvanishing section has a canonical inverse morphism. Under the
tensor-inverse/internal-Hom comparison, this is the corresponding inverse section. -/
@[stacks 01CY "inverse section"]
noncomputable def sectionOverInv (ℒ : X.Modules)
    [MonoidalCategory.isInvertibleObject ℒ]
    (s : ℒ.sections) :
    ℒ.over (sectionNonvanishingOpen X ℒ s) ⟶
      SheafOfModules.unit (X.ringCatSheaf.over (sectionNonvanishingOpen X ℒ s)) :=
  inv (sectionOverHom X ℒ s (sectionNonvanishingOpen X ℒ s))

/-- The restricted section followed by `sectionOverInv` is the identity. -/
theorem sectionOverHom_comp_inv (ℒ : X.Modules)
    [MonoidalCategory.isInvertibleObject ℒ]
    (s : ℒ.sections) :
    sectionOverHom X ℒ s (sectionNonvanishingOpen X ℒ s) ≫
        sectionOverInv X ℒ s = 𝟙 _ := sorry

/-- `sectionOverInv` followed by the restricted section is the identity. -/
theorem sectionOverInv_comp_hom (ℒ : X.Modules)
    [MonoidalCategory.isInvertibleObject ℒ]
    (s : ℒ.sections) :
    sectionOverInv X ℒ s ≫
        sectionOverHom X ℒ s (sectionNonvanishingOpen X ℒ s) = 𝟙 _ := sorry

namespace SectionNonvanishing

/-- The restricted nonvanishing section, bundled as a trivialization of the invertible module
by the structure module on its nonvanishing open. -/
@[stacks 01CY "bundled trivialization"]
noncomputable def trivialization (ℒ : X.Modules)
    [MonoidalCategory.isInvertibleObject ℒ]
    (s : ℒ.sections) :
    SheafOfModules.unit (X.ringCatSheaf.over (sectionNonvanishingOpen X ℒ s)) ≅
      ℒ.over (sectionNonvanishingOpen X ℒ s) where
  hom := sectionOverHom X ℒ s (sectionNonvanishingOpen X ℒ s)
  inv := sectionOverInv X ℒ s
  hom_inv_id := sectionOverHom_comp_inv X ℒ s
  inv_hom_id := sectionOverInv_comp_hom X ℒ s

/-- The forward map of the nonvanishing trivialization is the restricted section. -/
@[simp, stacks 01CY "bundled trivialization forward map"]
theorem trivialization_hom (ℒ : X.Modules)
    [MonoidalCategory.isInvertibleObject ℒ]
    (s : ℒ.sections) :
    (trivialization X ℒ s).hom =
      sectionOverHom X ℒ s (sectionNonvanishingOpen X ℒ s) := sorry

/-- The inverse map of the nonvanishing trivialization is `sectionOverInv`. -/
@[simp, stacks 01CY "bundled trivialization inverse map"]
theorem trivialization_inv (ℒ : X.Modules)
    [MonoidalCategory.isInvertibleObject ℒ]
    (s : ℒ.sections) :
    (trivialization X ℒ s).inv = sectionOverInv X ℒ s := sorry

end SectionNonvanishing

end Nonvanishing

end AlgebraicGeometry.RingedSpace
