module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Exact
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Flat.Availability
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Homology
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.LeftDerived
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Homology
import Mathlib.Tactic.CrossRefAttribute

/-!
# Exact flat scalar extension

@stack 0B67

For a flat map of commutative rings, extension of scalars is exact.  This leaf compares its
canonical derived-category action with the shared total-left-derived extension functor and
packages the induced homology comparison.  The comparison morphism is concrete data; its
invertibility is exposed both as an explicit proposition and as a convenience isomorphism.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.DerivedExtension.Flat

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The concrete comparison from exact extension of scalars to its derived extension. -/
@[stacks 0B67 "exact-flat derived extension comparison"]
noncomputable def mapDerivedCategoryComparison (f : R →+* S) (hf : f.Flat) :
    (ModuleCat.ExtendScalars.exact f hf).mapDerivedCategory ⟶
      ModuleCat.derivedExtensionOfScalars.{u, u, u} f :=
  ExactFunctor.LeftDerived.comparison
    (ModuleCat.ExtendScalars.exact f hf)
    (ModuleCat.derivedExtensionOfScalars f)
    (ModuleCat.derivedExtensionOfScalarsCounit f)
    (ModuleCat.derivedExtensionOfScalarsIsLeftDerivedOfModel
      (ModuleCat.derivedExtensionOfScalarsModel f))

/-- The exact-flat comparison is invertible.  This is a proposition so the remaining universal
property proof debt does not hide any non-Prop data. -/
@[stacks 0B67 "exact-flat derived extension comparison is invertible"]
theorem mapDerivedCategoryComparison_isIso (f : R →+* S) (hf : f.Flat) :
    IsIso (mapDerivedCategoryComparison f hf) := sorry

/-- An exact-flat comparison isomorphism built from an explicit invertibility certificate. -/
@[stacks 0B67 "exact-flat derived extension comparison isomorphism"]
noncomputable def mapDerivedCategoryComparisonIsoOf
    (f : R →+* S) (hf : f.Flat)
    (h : IsIso (mapDerivedCategoryComparison f hf)) :
    (ModuleCat.ExtendScalars.exact f hf).mapDerivedCategory ≅
      ModuleCat.derivedExtensionOfScalars.{u, u, u} f :=
  ExactFunctor.LeftDerived.comparisonIso
    (ModuleCat.ExtendScalars.exact f hf)
    (ModuleCat.derivedExtensionOfScalars f)
    (ModuleCat.derivedExtensionOfScalarsCounit f)
    (ModuleCat.derivedExtensionOfScalarsIsLeftDerivedOfModel
      (ModuleCat.derivedExtensionOfScalarsModel f))
    h

/-- The canonical exact-flat comparison isomorphism. -/
@[stacks 0B67 "canonical exact-flat derived extension comparison isomorphism"]
noncomputable def mapDerivedCategoryComparisonIso (f : R →+* S) (hf : f.Flat) :
    (ModuleCat.ExtendScalars.exact f hf).mapDerivedCategory ≅
      ModuleCat.derivedExtensionOfScalars.{u, u, u} f :=
  mapDerivedCategoryComparisonIsoOf f hf (mapDerivedCategoryComparison_isIso f hf)

/-- Raw exact-extension spelling of the bundled comparison owner, retained for source-facing
callers that use the raw extension functor.  The canonical additive and finite-limit facts are
fixed here so callers do not have to rebuild proof-local instances. -/
@[stacks 0B67 "raw exact-extension comparison isomorphism"]
noncomputable def rawMapDerivedCategoryComparisonIso
    (f : R →+* S) (hf : f.Flat) :
    letI : (ModuleCat.extendScalars.{u, u, u} f).Additive := inferInstance
    letI : Limits.PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} f) :=
      ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
    letI : Limits.PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} f) := inferInstance
    (ModuleCat.extendScalars.{u, u, u} f).mapDerivedCategory ≅
      ModuleCat.derivedExtensionOfScalars.{u, u, u} f :=
  letI : (ModuleCat.extendScalars.{u, u, u} f).Additive := inferInstance
  letI : Limits.PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} f) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  mapDerivedCategoryComparisonIso f hf

/-- Homology after exact scalar extension, oriented from the extended homology object to the
homology of the derived extension. -/
@[stacks 0B67 "exact-flat derived extension homology isomorphism"]
noncomputable def homologyIso (f : R →+* S) (hf : f.Flat)
    (K : DerivedCategory (ModuleCat R)) (i : ℤ) :
    (ModuleCat.extendScalars.{u, u, u} f).obj
        ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj K) ≅
      (DerivedCategory.homologyFunctor (ModuleCat S) i).obj
        (((ModuleCat.ExtendScalars.exact f hf).mapDerivedCategory).obj K) :=
  (ModuleCat.ExtendScalars.exact f hf).homologyIso K i |>.symm

/-- Homology after exact scalar extension, with the target expressed using the canonical derived
extension functor. -/
@[stacks 0B67 "exact-flat derived-extension homology isomorphism"]
noncomputable def derivedHomologyIso (f : R →+* S) (hf : f.Flat)
    (K : DerivedCategory (ModuleCat R)) (i : ℤ) :
    (ModuleCat.extendScalars.{u, u, u} f).obj
        ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj K) ≅
      (DerivedCategory.homologyFunctor (ModuleCat S) i).obj
        ((ModuleCat.derivedExtensionOfScalars.{u, u, u} f).obj K) :=
  homologyIso f hf K i ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat S) i).mapIso
      ((mapDerivedCategoryComparisonIso f hf).app K)

/-- Raw exact-extension spelling of the bundled homology owner, retained for source-facing
callers that use the raw extension functor.  The same canonical instance pins as above are
internal to this compatibility surface. -/
@[stacks 0B67 "raw exact-extension homology comparison"]
noncomputable def rawHomologyIso
    (f : R →+* S) (hf : f.Flat) (K : DerivedCategory (ModuleCat R)) (i : ℤ) :
    letI : (ModuleCat.extendScalars.{u, u, u} f).Additive := inferInstance
    letI : Limits.PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} f) :=
      ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
    letI : Limits.PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} f) := inferInstance
    (ModuleCat.extendScalars.{u, u, u} f).obj
        ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj K) ≅
      (DerivedCategory.homologyFunctor (ModuleCat S) i).obj
        (((ModuleCat.extendScalars.{u, u, u} f).mapDerivedCategory).obj K) :=
  letI : (ModuleCat.extendScalars.{u, u, u} f).Additive := inferInstance
  letI : Limits.PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} f) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  homologyIso f hf K i

/-- For a flat ring map, the canonical extension-of-homology comparison is invertible. -/
@[stacks 0DJD "flat derived-extension homology comparison"]
theorem homologyComparison_isIso (f : R →+* S) (hf : f.Flat)
    (K : DerivedCategory (ModuleCat R)) (i : ℤ) :
    IsIso (ModuleCat.derivedExtensionHomologyComparison f K i) := sorry

end CategoryTheory.ModuleCat.DerivedExtension.Flat
