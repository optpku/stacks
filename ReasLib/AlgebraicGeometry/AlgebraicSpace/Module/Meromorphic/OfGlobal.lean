/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Sections
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Invertible
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.UniverseLift.Morphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Section
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.Regular
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian

/-!
# Global sections as meromorphic sections

A global section of an `𝒪_X`-module determines a meromorphic section by
localizing at `1` on every étale object and applying the sheafification unit
into `𝒦_X(L)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules Opposite
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Universe-lift of a global section of an `𝒪_X`-module, obtained by applying
the lifted regular-section morphism to the tensor unit. -/
noncomputable def liftedGlobalSection {L : X.Modules} (s : L.sections) :
    (liftModule L).sections :=
  (liftModule L).unitHomEquiv
    ((liftedUnitIso X).inv ≫ liftModuleMap (regularSectionHom L s))

/-- The universe-lift of a global section is the image of `1` under the lifted
regular-section morphism. -/
theorem liftedGlobalSection_def {L : X.Modules} (s : L.sections) :
    liftedGlobalSection s =
      (liftModule L).unitHomEquiv
        ((liftedUnitIso X).inv ≫ liftModuleMap (regularSectionHom L s)) :=
  rfl

/-- Objectwise localization of a global section at the unit of `𝒮_X`. -/
noncomputable def toMeromorphicSectionPresheafObj {L : X.Modules}
    (s : L.sections) (U : (smallEtaleSite X)ᵒᵖ) :
    meromorphicSectionObj X L U :=
  LocalizedModule.mk
    (PresheafOfModules.sections.eval (liftedGlobalSection s) U)
    (1 : (regularStructureSections X).obj U)

/-- The objectwise localization of a global section is `LocalizedModule.mk` of
its universe lift at `1`. -/
theorem toMeromorphicSectionPresheafObj_eq {L : X.Modules} (s : L.sections)
    (U : (smallEtaleSite X)ᵒᵖ) :
    toMeromorphicSectionPresheafObj s U =
      LocalizedModule.mk
        (PresheafOfModules.sections.eval (liftedGlobalSection s) U)
        (1 : (regularStructureSections X).obj U) :=
  rfl

/-- Objectwise localization of a global section is compatible with étale
restriction. -/
theorem toMeromorphicSectionPresheaf_naturality {L : X.Modules} (s : L.sections) :
    ∀ ⦃U V : (smallEtaleSite X)ᵒᵖ⦄ (i : U ⟶ V),
      (meromorphicSectionPresheaf X L).map i
          (toMeromorphicSectionPresheafObj s U) =
        toMeromorphicSectionPresheafObj s V :=
  sorry

/-- The meromorphic-section presheaf section associated to a global section. -/
noncomputable def toMeromorphicSectionPresheaf {L : X.Modules} (s : L.sections) :
    PresheafOfModules.sections (meromorphicSectionPresheaf X L) :=
  PresheafOfModules.sectionsMk (toMeromorphicSectionPresheafObj s)
    (toMeromorphicSectionPresheaf_naturality s)

/-- The meromorphic-section presheaf section is the compatible family of
objectwise localizations at `1`. -/
theorem toMeromorphicSectionPresheaf_def {L : X.Modules} (s : L.sections) :
    toMeromorphicSectionPresheaf s =
      PresheafOfModules.sectionsMk (toMeromorphicSectionPresheafObj s)
        (toMeromorphicSectionPresheaf_naturality s) :=
  rfl

/-- Sheafification unit from the meromorphic-section presheaf of `L` into the
restriction of scalars of `𝒦_X(L)`. -/
noncomputable def meromorphicSectionSheafificationUnit (L : X.Modules) :
    meromorphicSectionPresheaf X L ⟶
      (PresheafOfModules.restrictScalars
          (PresheafOfModules.sheafificationRingMap (smallEtaleTopology X)
            (regularStructureSections X).localizationPresheaf)).obj
        (meromorphicSectionSheaf X L).val :=
  (PresheafOfModules.sheafificationAdjunction.{u + 1}
      (PresheafOfModules.sheafificationRingMap (smallEtaleTopology X)
        (regularStructureSections X).localizationPresheaf)).unit.app
    (meromorphicSectionPresheaf X L)

/-- The sheafification unit is the unit of module sheafification of the
meromorphic-section presheaf. -/
theorem meromorphicSectionSheafificationUnit_def (L : X.Modules) :
    meromorphicSectionSheafificationUnit L =
      (PresheafOfModules.sheafificationAdjunction.{u + 1}
          (PresheafOfModules.sheafificationRingMap (smallEtaleTopology X)
            (regularStructureSections X).localizationPresheaf)).unit.app
        (meromorphicSectionPresheaf X L) :=
  rfl

/-- The meromorphic section of an `𝒪_X`-module associated to a global section,
obtained by localizing at `1` and applying the sheafification unit. -/
noncomputable def toMeromorphicSection {L : X.Modules} (s : L.sections) :
    meromorphicSections X L :=
  PresheafOfModules.sectionsMap (M := meromorphicSectionPresheaf X L)
    (meromorphicSectionSheafificationUnit L)
    (toMeromorphicSectionPresheaf s)

/-- The meromorphic image of a global section is sheafification of its
objectwise localization at `1`. -/
theorem toMeromorphicSection_def {L : X.Modules} (s : L.sections) :
    toMeromorphicSection s =
      PresheafOfModules.sectionsMap (meromorphicSectionSheafificationUnit L)
        (toMeromorphicSectionPresheaf s) :=
  rfl

/-- A nonzero global section of an invertible module on an integral locally
Noetherian algebraic space remains regular as a meromorphic section. -/
theorem toMeromorphicSection_isRegular [IsLocallyNoetherian X] [IsIntegral X]
    {L : X.Modules} [isInvertibleObject L] (s : L.sections) (hs : s ≠ 0) :
    IsRegularMeromorphicSection X L (toMeromorphicSection s) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
