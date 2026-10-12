/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.Comparison
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Coreflective
public import Mathlib.CategoryTheory.Adjunction.Restrict

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.SupportedOn

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- Derived sections with specialization-stable support over a Noetherian ring
preserve bounded-below derived objects. -/
theorem derivedSectionsMapsToPlus
    (T : Set (PrimeSpectrum A)) [Fact (StableUnderSpecialization T)] :
    (DerivedCategory.TStructure.t.plus : ObjectProperty (DerivedCategory (ModuleCat.{u} A))) ≤
      (DerivedCategory.TStructure.t.plus : ObjectProperty (DerivedCategory (category T))).inverseImage
        (derivedSections T) := sorry

/-- The restriction of derived sections with support in `T` to bounded-below
derived categories. -/
noncomputable def derivedSectionsPlus
    (T : Set (PrimeSpectrum A)) [Fact (StableUnderSpecialization T)] :
    DerivedCategory.Plus (ModuleCat.{u} A) ⥤ DerivedCategory.Plus (category T) :=
  ObjectProperty.FullSubcategory.restrict (derivedSections T) (derivedSectionsMapsToPlus T)

/-- Bounded-below derived sections, valued in the full subcategory of ambient
derived objects whose cohomology is supported on `T`. -/
noncomputable abbrev boundedBelowDerivedSections
    (T : Set (PrimeSpectrum A)) [Fact (StableUnderSpecialization T)] :
    DerivedCategory.Plus (ModuleCat.{u} A) ⥤
      DerivedCategory.Plus.CohomologyIn
        (ModuleCat.supportedOn T : ObjectProperty (ModuleCat.{u} A)) :=
  derivedSectionsPlus T ⋙ DerivedCategory.Plus.CohomologyIn.Comparison.functor
    (ModuleCat.supportedOn T : ObjectProperty (ModuleCat.{u} A))

/-- Over a Noetherian ring, bounded-below derived sections with specialization-stable
support are right adjoint to the inclusion of objects with supported cohomology. -/
noncomputable def boundedBelowDerivedSectionsAdjunction
    (T : Set (PrimeSpectrum A)) [Fact (StableUnderSpecialization T)] :
      (DerivedCategory.Plus.cohomologyIn
        (ModuleCat.supportedOn T : ObjectProperty (ModuleCat.{u} A))).ι ⊣
      boundedBelowDerivedSections T :=
  -- Local instance justification (defeq pin): transport the canonical Comparison.functor equivalence to the explicit lift of ExactFunctor.Derived.Plus.functor (exactInclusion T), whose instance head is needed by inclusionAdjunctionOfLift.
  letI : Functor.IsEquivalence
      ((DerivedCategory.Plus.cohomologyIn
          (ModuleCat.supportedOn T : ObjectProperty (ModuleCat.{u} A))).lift
        (ExactFunctor.Derived.Plus.functor (exactInclusion T))
        (DerivedCategory.Plus.CohomologyIn.Comparison.obj_mem
          (ModuleCat.supportedOn T : ObjectProperty (ModuleCat.{u} A)))) := by
    exact Functor.isEquivalence_of_iso
      (F := DerivedCategory.Plus.CohomologyIn.Comparison.functor
        (ModuleCat.supportedOn T : ObjectProperty (ModuleCat.{u} A)))
      (G := (DerivedCategory.Plus.cohomologyIn
        (ModuleCat.supportedOn T : ObjectProperty (ModuleCat.{u} A))).lift
          (ExactFunctor.Derived.Plus.functor (exactInclusion T))
          (DerivedCategory.Plus.CohomologyIn.Comparison.obj_mem
            (ModuleCat.supportedOn T : ObjectProperty (ModuleCat.{u} A))))
      (Iso.refl _)
  ObjectProperty.FullSubcategory.inclusionAdjunctionOfLift
    ((derivedAdjunction T).restrictFullyFaithful
      (DerivedCategory.TStructure.t.plus.fullyFaithfulι)
      (DerivedCategory.TStructure.t.plus.fullyFaithfulι)
      (ExactFunctor.Derived.Plus.compιIso (exactInclusion T)).symm
      (ObjectProperty.FullSubcategory.restrict.compιIso
        (derivedSections T) (derivedSectionsMapsToPlus T)).symm)
    (DerivedCategory.Plus.CohomologyIn.Comparison.obj_mem
      (ModuleCat.supportedOn T : ObjectProperty (ModuleCat.{u} A)))

/-- Forgetting the supported bounded-below target identifies derived sections with
the ambient derived inclusion of unbounded derived sections on the same object. -/
noncomputable def boundedBelowDerivedSectionsValueIso
    (T : Set (PrimeSpectrum A)) [Fact (StableUnderSpecialization T)]
    (K : DerivedCategory.Plus (ModuleCat.{u} A)) :
    DerivedCategory.Plus.ι.obj ((boundedBelowDerivedSections T).obj K).obj ≅
      ((ModuleCat.supportedOn T : ObjectProperty (ModuleCat.{u} A)).ι.mapDerivedCategory).obj
        ((derivedSections T).obj (DerivedCategory.Plus.ι.obj K)) :=
  DerivedCategory.Plus.ι.mapIso
      ((DerivedCategory.Plus.CohomologyIn.Comparison.compιIso
        (ModuleCat.supportedOn T : ObjectProperty (ModuleCat.{u} A))).app
          ((derivedSectionsPlus T).obj K)) ≪≫
    (DerivedCategory.Plus.CohomologyIn.Comparison.Ambient.compιIso
      (ModuleCat.supportedOn T : ObjectProperty (ModuleCat.{u} A))).app
        ((derivedSectionsPlus T).obj K) ≪≫
    ((ModuleCat.supportedOn T : ObjectProperty (ModuleCat.{u} A)).ι.mapDerivedCategory).mapIso
      ((ObjectProperty.FullSubcategory.restrict.compιIso
        (derivedSections T) (derivedSectionsMapsToPlus T)).app K)

/-- Unbounded derived sections, valued in the full subcategory of ambient
derived objects whose cohomology is supported on `T`. -/
noncomputable abbrev derivedSectionsWithSupportedCohomology
    (T : Set (PrimeSpectrum A)) [Fact (StableUnderSpecialization T)] :
    DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory.CohomologyIn
        (ModuleCat.supportedOn T : ObjectProperty (ModuleCat.{u} A)) :=
  derivedSections T ⋙ DerivedCategory.CohomologyIn.Comparison.functor
    (ModuleCat.supportedOn T : ObjectProperty (ModuleCat.{u} A))

/-- Over a finite-dimensional Noetherian ring, unbounded derived sections with
specialization-stable support are right adjoint to the supported-cohomology inclusion. -/
noncomputable def derivedSectionsWithSupportedCohomologyAdjunction
    (T : Set (PrimeSpectrum A)) [Fact (StableUnderSpecialization T)]
    [Fact (∃ d : ℕ, Ring.KrullDimLE d A)] :
    (DerivedCategory.cohomologyIn
        (ModuleCat.supportedOn T : ObjectProperty (ModuleCat.{u} A))).ι ⊣
      derivedSectionsWithSupportedCohomology T :=
  ObjectProperty.FullSubcategory.inclusionAdjunctionOfLift
    (((derivedAdjunction T).ofNatIsoLeft
      (Iso.refl _ : derivedInclusion T ≅
        (ModuleCat.supportedOn T : ObjectProperty (ModuleCat.{u} A)).ι.mapDerivedCategory)) :
      (ModuleCat.supportedOn T : ObjectProperty (ModuleCat.{u} A)).ι.mapDerivedCategory ⊣
        derivedSections T)
    (DerivedCategory.CohomologyIn.Comparison.obj_mem
      (ModuleCat.supportedOn T : ObjectProperty (ModuleCat.{u} A)))

end CategoryTheory.ModuleCat.SupportedOn
