module

import StacksCheckRecall
import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.AlgebraizationSituation

open CategoryTheory

universe u v

/- Situation 52.10.1 -/
@[stacks 0EFU] #check
  (@Ideal.LocalCohomology.AlgebraizationSituation :
    {A : Type u} → [CommRing A] → [IsNoetherianRing A] →
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))] →
      MonoidalClosed (DerivedCategory (ModuleCat.{u} A)) →
      Ideal A → (M : Type v) → [AddCommGroup M] → [Module A M] →
      [Module.Finite A M] → Set (PrimeSpectrum A) → ℤ → ℤ → Prop)
