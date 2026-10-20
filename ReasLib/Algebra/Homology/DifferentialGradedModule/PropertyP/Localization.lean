/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived
public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyP.Resolution
public import ReasLib.CategoryTheory.ObjectProperty.Localization.Equivalence.Cover

/-!
# Property-(P) models for the DG-module derived category

This leaf makes the full subcategory of property-(P) homotopy objects a reusable localization
model of the whole derived category.  Constructions defined naturally on property-(P) objects
can therefore descend through the standard localization API without selecting resolutions in
their public data.
-/

@[expose] public section

noncomputable section

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory

universe u v

namespace DifferentialGradedModule.Homotopy

variable {R : Type u} [CommRing R]

/-- Property-(P) objects in the homotopy category of right DG `A`-modules. -/
@[stacks 09KP "property-P objects in the DG homotopy category"]
def propertyP (A : CochainDGAlgebra.{u, v} R) :
    ObjectProperty (K R (DifferentialGradedModule.{u, v} A)) :=
  fun P => DifferentialGradedModule.HasPropertyP A P.obj

namespace PropertyP

/-- Membership in the homotopy-category property-(P) subcategory is exactly strict
property-(P) for the underlying DG module. -/
@[simp]
theorem propertyP_iff (A : CochainDGAlgebra.{u, v} R)
    (P : K R (DifferentialGradedModule.{u, v} A)) :
    propertyP A P ↔ DifferentialGradedModule.HasPropertyP A P.obj := sorry

/-- Quasi-isomorphisms restricted to property-(P) homotopy objects. -/
abbrev qis (A : CochainDGAlgebra.{u, v} R) :=
  fullSubcategoryLocalizationSystem (propertyP A)
    (DifferentialGradedModule.quasiIso A)

/-- The derived-category localization restricted to property-(P) homotopy objects. -/
@[stacks 09KP "property-P localization model of the DG derived category",
  stacks 0CS6 "property-P localization for derived Hom descent"]
noncomputable abbrev localization (A : CochainDGAlgebra.{u, v} R) :=
  (propertyP A).ι ⋙ DifferentialGradedModule.Derived.Q A

/-- Every DG homotopy object admits a left resolution by a property-(P) object. -/
@[stacks 09KP "property-P left resolutions"]
instance hasLeftResolutions (A : CochainDGAlgebra.{u, v} R) :
    (fullSubcategoryLocalizerMorphism (propertyP A)
      (DifferentialGradedModule.quasiIso A)).HasLeftResolutions := sorry

/-- The property-(P) inclusion localizer is a localized equivalence. This specialized instance
keeps downstream typeclass search on the canonical property-(P) owner. -/
@[stacks 0CS6 "property-P localized equivalence for derived Hom descent"]
instance (priority := 1100) localizerIsLocalizedEquivalence
    (A : CochainDGAlgebra.{u, v} R) :
    (fullSubcategoryLocalizerMorphism (propertyP A)
      (DifferentialGradedModule.quasiIso A)).IsLocalizedEquivalence := sorry

/-- The derived localization restricted to property-(P) homotopy objects is a localization. -/
@[stacks 09KP "property-P objects localize to the DG derived category",
  stacks 0CS6 "property-P localization used for derived Hom descent"]
noncomputable instance localizationIsLocalization (A : CochainDGAlgebra.{u, v} R) :
    (localization A).IsLocalization (qis A) := sorry

section Checks

variable (A : CochainDGAlgebra.{u, v} R)

#synth (fullSubcategoryLocalizerMorphism (propertyP A)
  (DifferentialGradedModule.quasiIso A)).HasLeftResolutions
#synth (fullSubcategoryLocalizerMorphism (propertyP A)
  (DifferentialGradedModule.quasiIso A)).IsLocalizedEquivalence
#synth (localization A).IsLocalization (qis A)

end Checks

end PropertyP
end DifferentialGradedModule.Homotopy
