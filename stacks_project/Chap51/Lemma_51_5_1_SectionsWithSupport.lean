/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Module.SectionsWithSupport
public import ReasLib.Algebra.Category.ModuleCat.Support

@[expose] public section

universe u v w

namespace Module

variable {A : Type u} [CommRing A]
variable {M : Type v} [AddCommGroup M] [Module A M]

/- Compatibility checks for the promoted module-support API. -/
#check (Module.elementSupport :
  ∀ (A : Type u) [CommRing A] {M : Type v} [AddCommGroup M] [Module A M],
    M → Set (PrimeSpectrum A))
#check (Module.sectionsWithSupport :
  ∀ {A : Type u} [CommRing A] (T : Set (PrimeSpectrum A)) (M : Type v)
    [AddCommGroup M] [Module A M], Submodule A M)
#check (Module.sectionsWithSupport_eq_top_iff_support_subset :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T)
    (M : Type v) [AddCommGroup M] [Module A M],
    Module.sectionsWithSupport T M = ⊤ ↔ Module.support A M ⊆ T)

end Module

namespace CategoryTheory.ModuleCat

variable {A : Type u} [CommRing A]

/- Compatibility checks for the promoted categorical support API. -/
#check (CategoryTheory.ModuleCat.supportedOn :
  ∀ {A : Type u} [CommRing A] (T : Set (PrimeSpectrum A)),
    ObjectProperty (ModuleCat.{v} A))
#check (CategoryTheory.ModuleCat.supportedOnIsSerreClass :
  ∀ {A : Type u} [CommRing A] (T : Set (PrimeSpectrum A)),
    ObjectProperty.IsSerreClass
      (CategoryTheory.ModuleCat.supportedOn T : ObjectProperty (ModuleCat.{v} A)))

end CategoryTheory.ModuleCat
