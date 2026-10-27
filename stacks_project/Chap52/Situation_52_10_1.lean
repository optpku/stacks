/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

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
      CategoryTheory.DerivedCategory.CanonicalClosedPresentation (A := A) →
      Ideal A → (M : Type v) → [AddCommGroup M] → [Module A M] →
      [Module.Finite A M] → Set (PrimeSpectrum A) → ℤ → ℤ → Prop)
