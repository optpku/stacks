/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.IdealPower.BaseChange
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Adjunction
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Flat
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Adjunction

@[expose] public section

/-!
# Derived base change for ideal-power torsion

This file restricts derived extension and restriction of scalars to objects
whose cohomology is ideal-power torsion, and records their restricted
adjunction.
-/

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.IdealPower.DerivedBaseChange

variable {A B : Type u} [CommRing A] [CommRing B]

/-- Flat derived extension of scalars preserves ideal-power-torsion
cohomology. -/
theorem mapsExtension (f : A →+* B) (I : Ideal A) (hf : f.Flat) :
    DerivedCategory.cohomologyIn
        (fun M : ModuleCat A ↦ Module.IsIdealPowerTorsion I M) ≤
      (DerivedCategory.cohomologyIn
          (fun M : ModuleCat B ↦ Module.IsIdealPowerTorsion (I.map f) M)).inverseImage
        (ModuleCat.derivedExtensionOfScalars f) := sorry

/-- Derived extension of scalars restricted to objects with ideal-power-torsion
cohomology. -/
noncomputable def extension (f : A →+* B) (I : Ideal A) (hf : f.Flat) :
    DerivedCategory.CohomologyIn
        (fun M : ModuleCat A ↦ Module.IsIdealPowerTorsion I M) ⥤
      DerivedCategory.CohomologyIn
        (fun M : ModuleCat B ↦ Module.IsIdealPowerTorsion (I.map f) M) :=
  ObjectProperty.FullSubcategory.restrict
    (ModuleCat.derivedExtensionOfScalars f) (mapsExtension f I hf)

/-- Forgetting the torsion condition identifies restricted derived extension
with the ambient derived extension functor on objects. -/
theorem extension_obj (f : A →+* B) (I : Ideal A) (hf : f.Flat)
    (K : DerivedCategory.CohomologyIn
      (fun M : ModuleCat A ↦ Module.IsIdealPowerTorsion I M)) :
    ((extension f I hf).obj K).obj =
      (ModuleCat.derivedExtensionOfScalars f).obj K.obj := sorry

/-- Derived restriction of scalars preserves ideal-power-torsion
cohomology. -/
theorem mapsRestriction (f : A →+* B) (I : Ideal A) :
    DerivedCategory.cohomologyIn
        (fun M : ModuleCat B ↦ Module.IsIdealPowerTorsion (I.map f) M) ≤
      (DerivedCategory.cohomologyIn
          (fun M : ModuleCat A ↦ Module.IsIdealPowerTorsion I M)).inverseImage
        (ModuleCat.derivedRestrictionOfScalars f) := sorry

/-- Derived restriction of scalars restricted to objects with
ideal-power-torsion cohomology. -/
noncomputable def restriction (f : A →+* B) (I : Ideal A) :
    DerivedCategory.CohomologyIn
        (fun M : ModuleCat B ↦ Module.IsIdealPowerTorsion (I.map f) M) ⥤
      DerivedCategory.CohomologyIn
        (fun M : ModuleCat A ↦ Module.IsIdealPowerTorsion I M) :=
  ObjectProperty.FullSubcategory.restrict
    (ModuleCat.derivedRestrictionOfScalars f) (mapsRestriction f I)

/-- Forgetting the torsion condition identifies restricted derived restriction
with the ambient derived restriction functor on objects. -/
theorem restriction_obj (f : A →+* B) (I : Ideal A)
    (L : DerivedCategory.CohomologyIn
      (fun M : ModuleCat B ↦ Module.IsIdealPowerTorsion (I.map f) M)) :
    ((restriction f I).obj L).obj =
      (ModuleCat.derivedRestrictionOfScalars f).obj L.obj := sorry

/-- The canonical derived extension–restriction adjunction restricted to
ideal-power-torsion cohomology. -/
noncomputable def adjunction (f : A →+* B) (I : Ideal A) (hf : f.Flat) :
    extension f I hf ⊣ restriction f I :=
  ObjectProperty.FullSubcategory.adjunction
    (ModuleCat.derivedExtensionOfScalars f)
    (ModuleCat.derivedRestrictionOfScalars f)
    (ModuleCat.derivedExtensionRestrictionAdjunction f)
    (mapsExtension f I hf) (mapsRestriction f I)

/-- Under flatness, finite generation, and the quotient comparison, the unit
and counit of derived base change on ideal-power-torsion cohomology are
pointwise isomorphisms. -/
theorem unitCounit_isIso (f : A →+* B) (I : Ideal A) (hI : I.FG)
    (hf : f.Flat) (hquot : Function.Bijective (f.quotientByIdeal I)) :
    (∀ K : DerivedCategory.CohomologyIn
        (fun M : ModuleCat A ↦ Module.IsIdealPowerTorsion I M),
      IsIso ((adjunction f I hf).unit.app K)) ∧
    (∀ L : DerivedCategory.CohomologyIn
        (fun M : ModuleCat B ↦ Module.IsIdealPowerTorsion (I.map f) M),
      IsIso ((adjunction f I hf).counit.app L)) := sorry

end CategoryTheory.ModuleCat.IdealPower.DerivedBaseChange
