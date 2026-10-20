module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Exact
public import ReasLib.Algebra.Category.ModuleCat.FinitePresentation
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Functor.Exact.Plus
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RingHom.Flat

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open ExactFunctor.Derived
open DerivedCategory.Plus
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.LocalizationAtPrime

/-- Extension of scalars to a prime localization preserves finite presentation. -/
theorem mapsFinitePresentation
    {A : Type u} [CommRing A] (p : PrimeSpectrum A) :
    ModuleCat.isFinitePresentation A ≤
      (ModuleCat.isFinitePresentation (Localization.AtPrime p.asIdeal)).inverseImage
        (ModuleCat.extendScalars (algebraMap A (Localization.AtPrime p.asIdeal))) := sorry

open Plus in
open CohomologyIn in
/-- The bounded-below coherent derived localization functor at a prime. -/
noncomputable def coherent
    {A : Type u} [CommRing A] (p : PrimeSpectrum A) :
    D⁺[ModuleCat.isFinitePresentation A] ⥤
    D⁺[ModuleCat.isFinitePresentation (Localization.AtPrime p.asIdeal)] :=
  functor
    (ModuleCat.ExtendScalars.exact (algebraMap A (Localization.AtPrime p.asIdeal))
      (RingHom.flat_algebraMap_iff.mpr
        (IsLocalization.flat (Localization.AtPrime p.asIdeal) p.asIdeal.primeCompl)))
    (ModuleCat.isFinitePresentation A)
    (ModuleCat.isFinitePresentation (Localization.AtPrime p.asIdeal))
    (mapsFinitePresentation p)

open Plus in
/-- Forgetting the coherent-cohomology property identifies prime localization with exact
bounded-below derived extension of scalars. -/
theorem coherent_obj
    {A : Type u} [CommRing A] (p : PrimeSpectrum A)
    (K : D⁺[ModuleCat.isFinitePresentation A]) :
    ((coherent p).obj K).obj =
      (functor
        (ModuleCat.ExtendScalars.exact (algebraMap A (Localization.AtPrime p.asIdeal))
          (RingHom.flat_algebraMap_iff.mpr
            (IsLocalization.flat
              (Localization.AtPrime p.asIdeal) p.asIdeal.primeCompl)))).obj K.obj := sorry

end CategoryTheory.DerivedCategory.LocalizationAtPrime
