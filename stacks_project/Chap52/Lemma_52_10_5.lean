/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.AlgebraizationSituation
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

namespace Ideal.LocalCohomology.AlgebraizationSituation

/- Lemma 52.10.5: if `I ≤ a`, the Noetherian ring `A` has a dualizing complex,
`HasDimensionLE I d` holds, and the stated strict depth alternative holds for primes
`p ∉ V(I)` and `q ∈ V(p) ∩ V(a)`, then `(A, I, V(a), M, s, d)` is an
algebraization situation. -/
@[stacks 0EFW] #check (Ideal.LocalCohomology.AlgebraizationSituation.of_zeroLocus :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (I a : Ideal A) (hIa : I ≤ a) (s d : ℤ)
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H)
    (h_cd : HasDimensionLE I d)
    (h_depth : ∀ p q : PrimeSpectrum A,
      p ∉ PrimeSpectrum.zeroLocus (I : Set A) → p.asIdeal ≤ q.asIdeal →
        q ∈ PrimeSpectrum.zeroLocus (a : Set A) →
          (s : EInt) <
              ((WithTop.map Int.ofNat
                (moduleDepth (Localization.AtPrime p.asIdeal)
                  (LocalizedModule.AtPrime p.asIdeal M)) : WithTop ℤ) : EInt) ∨
            ((d + s : ℤ) : EInt) <
              ((WithTop.map Int.ofNat
                (moduleDepth (Localization.AtPrime p.asIdeal)
                  (LocalizedModule.AtPrime p.asIdeal M)) : WithTop ℤ) : EInt) +
                WithBot.map (WithTop.map Int.ofNat)
                  (ringKrullDim (p.asIdeal.quotientAtPrime q))),
    AlgebraizationSituation H I M (PrimeSpectrum.zeroLocus (a : Set A)) s d)

end Ideal.LocalCohomology.AlgebraizationSituation
