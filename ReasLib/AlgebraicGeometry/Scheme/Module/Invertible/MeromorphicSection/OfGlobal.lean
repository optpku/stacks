module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.MeromorphicSection.Denominator

/-!
# Meromorphic sections induced by global sections

This file constructs the meromorphic image of a global section of an invertible module and
records that nonzero global sections remain nonzero after scalar extension.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Map a global section of a scheme module to the corresponding meromorphic section. -/
noncomputable def toMeromorphicSection {X : Scheme.{u}} (ℒ : X.Modules)
    (s : ℒ.sections) : X.toLocallyRingedSpace.meromorphicSections ℒ :=
  SheafOfModules.sectionsMap (M := ℒ) (Scheme.meromorphicSectionUnit ℒ) s

/-- A nonzero section of an invertible module remains nonzero as a meromorphic section. -/
theorem toMeromorphicSection_ne_zero {X : Scheme.{u}} (ℒ : X.Modules) [Invertible ℒ]
    (s : ℒ.sections) (hs : s ≠ 0) : toMeromorphicSection ℒ s ≠ 0 := sorry

end AlgebraicGeometry.Scheme.Modules
