/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.Derived
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Flat
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.RingTheory.KrullDimension.Basic

@[expose] public section

open CategoryTheory
open ObjectProperty.FullSubcategory
open ModuleCat.DerivedExtension.Flat

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.SupportedOn

variable {A B : Type u} [CommRing A] [CommRing B]

/-- The inverse image in `PrimeSpectrum B` of a support `T` along `f : A →+* B`. -/
abbrev inverseImageSupport (f : A →+* B) (T : Set (PrimeSpectrum A)) :
    Set (PrimeSpectrum B) :=
  PrimeSpectrum.comap f ⁻¹' T

/-- Membership in the inverse-image support is membership after contraction of primes. -/
theorem mem_inverseImageSupport (f : A →+* B) (T : Set (PrimeSpectrum A))
    (q : PrimeSpectrum B) :
    q ∈ inverseImageSupport f T ↔ PrimeSpectrum.comap f q ∈ T := sorry

/-- Inverse image along the spectral map preserves stability under specialization. -/
theorem inverseImageSupport_stable (f : A →+* B) (T : Set (PrimeSpectrum A))
    (hT : StableUnderSpecialization T) :
    StableUnderSpecialization (inverseImageSupport f T) := sorry

/-- Scalar extension carries modules supported on `T` to modules supported on its inverse image. -/
theorem extendScalars_mapsSupportedOn (f : A →+* B) (T : Set (PrimeSpectrum A)) :
    (ModuleCat.supportedOn T : ObjectProperty (ModuleCat.{u} A)) ≤
      (ModuleCat.supportedOn (inverseImageSupport f T) :
        ObjectProperty (ModuleCat.{u} B)).inverseImage
        (ModuleCat.extendScalars.{u, u, u} f) := sorry

/-- Scalar extension restricted to modules with the corresponding supports. -/
noncomputable def extendScalars (f : A →+* B) (T : Set (PrimeSpectrum A)) :
    category T ⥤ category (inverseImageSupport f T) :=
  ObjectProperty.FullSubcategory.restrict (ModuleCat.extendScalars.{u, u, u} f)
    (extendScalars_mapsSupportedOn f T)

/-- Restricted scalar extension is exact when the ring homomorphism is flat. -/
theorem extendScalars_exact (f : A →+* B) (hf : f.Flat)
    (T : Set (PrimeSpectrum A)) :
    exactFunctor (category T) (category (inverseImageSupport f T))
      (extendScalars f T) := sorry

/-- Flat scalar extension between the supported module categories, bundled as an exact functor. -/
noncomputable def exactExtendScalars (f : A →+* B) (hf : f.Flat)
    (T : Set (PrimeSpectrum A)) :
    category T ⥤ₑ category (inverseImageSupport f T) :=
  ⟨extendScalars f T, extendScalars_exact f hf T⟩

/-- After forgetting supports, restricted flat scalar extension is ordinary scalar extension. -/
noncomputable def exactExtendScalarsCompInclusionIso (f : A →+* B) (hf : f.Flat)
    (T : Set (PrimeSpectrum A)) :
    (exactExtendScalars f hf T).comp (exactInclusion (inverseImageSupport f T)) ≅
      (exactInclusion T).comp (ModuleCat.ExtendScalars.exact f hf) :=
  ObjectProperty.isoMk (exactFunctor (category T) (ModuleCat.{u} B))
    (restrict.compιIso
      (ModuleCat.extendScalars.{u, u, u} f) (extendScalars_mapsSupportedOn f T))

/-- The ambient derived object underlying restricted flat scalar extension is canonically
the ordinary derived extension of the ambient supported object. -/
noncomputable def exactExtendScalarsAmbientIso (f : A →+* B) (hf : f.Flat)
    (T : Set (PrimeSpectrum A)) (K : DerivedCategory (category T)) :
    (derivedInclusion (inverseImageSupport f T)).obj
        ((exactExtendScalars f hf T).mapDerivedCategory.obj K) ≅
      (ModuleCat.derivedExtensionOfScalars f).obj ((derivedInclusion T).obj K) :=
  (ExactFunctor.MapDerivedCategory.compObjIso
      (exactExtendScalars f hf T) (exactInclusion (inverseImageSupport f T)) K).symm ≪≫
    (ExactFunctor.MapDerivedCategory.mapIso
      (exactExtendScalarsCompInclusionIso f hf T)).app K ≪≫
    ExactFunctor.MapDerivedCategory.compObjIso
      (exactInclusion T) (ModuleCat.ExtendScalars.exact f hf) K ≪≫
    (mapDerivedCategoryComparisonIso f hf).app
      ((derivedInclusion T).obj K)

/-- The canonical flat base-change map from derived sections supported on `T`, after derived
scalar extension, to derived sections supported on the inverse image of `T`. -/
noncomputable def flatBaseChangeMap (f : A →+* B) (hf : f.Flat)
    (T : Set (PrimeSpectrum A)) (K : DerivedCategory (ModuleCat.{u} A)) :
    (ModuleCat.derivedExtensionOfScalars f).obj
        ((derivedSections T ⋙ derivedInclusion T).obj K) ⟶
      (derivedSections (inverseImageSupport f T) ⋙
        derivedInclusion (inverseImageSupport f T)).obj
          ((ModuleCat.derivedExtensionOfScalars f).obj K) :=
  let X := (exactExtendScalars f hf T).mapDerivedCategory.obj ((derivedSections T).obj K)
  let e := exactExtendScalarsAmbientIso f hf T ((derivedSections T).obj K)
  e.inv ≫ (derivedInclusion (inverseImageSupport f T)).map
    (derivedHomEquiv (inverseImageSupport f T) X
      ((ModuleCat.derivedExtensionOfScalars f).obj K)
      (e.hom ≫ (ModuleCat.derivedExtensionOfScalars f).map
        ((derivedAdjunction T).counit.app K)))

/-- The flat base-change map is characterized by compatibility with the two derived-section
counits. -/
theorem flatBaseChangeMap_comp_counit (f : A →+* B) (hf : f.Flat)
    (T : Set (PrimeSpectrum A)) (K : DerivedCategory (ModuleCat.{u} A)) :
    flatBaseChangeMap f hf T K ≫
        (derivedAdjunction (inverseImageSupport f T)).counit.app
          ((ModuleCat.derivedExtensionOfScalars f).obj K) =
      (ModuleCat.derivedExtensionOfScalars f).map
        ((derivedAdjunction T).counit.app K) := sorry

/-- The flat base-change map is invertible for bounded-below objects over Noetherian rings
when the support is stable under specialization. -/
theorem flatBaseChangeMapIsIsoOfBoundedBelow [IsNoetherianRing A] [IsNoetherianRing B]
    (f : A →+* B) (hf : f.Flat) (T : Set (PrimeSpectrum A))
    (hT : StableUnderSpecialization T) (K : DerivedCategory.Plus (ModuleCat.{u} A)) :
    IsIso (flatBaseChangeMap f hf T K.obj) := sorry

/-- The bounded-below flat base-change isomorphism inferred from specialization stability. -/
instance flatBaseChangeMapIsIsoOfBoundedBelowInstance
    [IsNoetherianRing A] [IsNoetherianRing B] (f : A →+* B) (hf : f.Flat)
    (T : Set (PrimeSpectrum A)) [Fact (StableUnderSpecialization T)]
    (K : DerivedCategory.Plus (ModuleCat.{u} A)) :
    IsIso (flatBaseChangeMap f hf T K.obj) :=
  flatBaseChangeMapIsIsoOfBoundedBelow f hf T Fact.out K

/-- The flat base-change map is invertible for all derived objects when both Noetherian rings
have finite Krull dimension and the support is stable under specialization. -/
theorem flatBaseChangeMapIsIsoOfFiniteKrullDim [IsNoetherianRing A] [IsNoetherianRing B]
    (f : A →+* B) (hf : f.Flat) (T : Set (PrimeSpectrum A))
    (hT : StableUnderSpecialization T)
    (hfiniteA : ∃ d : ℕ, Ring.KrullDimLE d A)
    (hfiniteB : ∃ d : ℕ, Ring.KrullDimLE d B)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    IsIso (flatBaseChangeMap f hf T K) := sorry

/-- The unbounded flat base-change isomorphism inferred from specialization stability and
finite Krull dimension of the source and target rings. -/
instance flatBaseChangeMapIsIsoOfFiniteKrullDimInstance
    [IsNoetherianRing A] [IsNoetherianRing B] (f : A →+* B) (hf : f.Flat)
    (T : Set (PrimeSpectrum A)) [Fact (StableUnderSpecialization T)]
    [Fact (∃ d : ℕ, Ring.KrullDimLE d A)] [Fact (∃ d : ℕ, Ring.KrullDimLE d B)]
    (K : DerivedCategory (ModuleCat.{u} A)) :
    IsIso (flatBaseChangeMap f hf T K) :=
  flatBaseChangeMapIsIsoOfFiniteKrullDim f hf T
    (Fact.out : StableUnderSpecialization T)
    (Fact.out : ∃ d : ℕ, Ring.KrullDimLE d A)
    (Fact.out : ∃ d : ℕ, Ring.KrullDimLE d B) K

end CategoryTheory.ModuleCat.SupportedOn
