/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Catenary.Universally
public import ReasLib.RingTheory.FormalFiber.CohenMacaulay
public import ReasLib.RingTheory.FormalFiber.PRing
public import ReasLib.RingTheory.Ideal.Localization
public import ReasLib.RingTheory.Depth.Localization
public import Mathlib.Algebra.Homology.LocalCohomology
public import Mathlib.Algebra.Regular.Defs

@[expose] public section

open CategoryTheory
open scoped ENat

noncomputable section

universe u

namespace Module.LocalCohomology

/-- Finiteness of the first two local-cohomology modules of a principal regular
quotient is equivalent to a strict depth and quotient-dimension bound along
the corresponding prime pairs. -/
theorem finite_one_two_iff_depth_add_quotientDim
    {A : Type u} [CommRing A] [UniversallyCatenaryRing.{u, u} A]
    (𝔞 : Ideal A) (f : A) (h_f_mem : f ∈ 𝔞) (h_f_regular : IsRegular f)
    (h_formal : ∀ p : PrimeSpectrum A,
      FieldAlgebraProperty.cohenMacaulay.HoldsOnFormalFibers
        (Localization.AtPrime p.asIdeal)) :
    (Module.Finite A
        ((localCohomology 𝔞 1).obj
          (ModuleCat.of A
            (A ⧸ (Ideal.span ({f} : Set A) • (⊤ : Submodule A A))))) ∧
      Module.Finite A
        ((localCohomology 𝔞 2).obj
          (ModuleCat.of A
            (A ⧸ (Ideal.span ({f} : Set A) • (⊤ : Submodule A A)))))) ↔
      ∀ p q : PrimeSpectrum A,
        p ∈ PrimeSpectrum.zeroLocus (Ideal.span ({f} : Set A) : Set A) →
          p ∉ PrimeSpectrum.zeroLocus (𝔞 : Set A) →
            q ∈ PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
              PrimeSpectrum.zeroLocus (𝔞 : Set A) →
              (.some (2 : ℕ∞) : WithBot ℕ∞) <
                (.some (moduleDepth (Localization.AtPrime p.asIdeal)
                  (LocalizedModule.AtPrime p.asIdeal
                    (A ⧸ (Ideal.span ({f} : Set A) • (⊤ : Submodule A A))))) :
                  WithBot ℕ∞) +
                  ringKrullDim (p.asIdeal.quotientAtPrime q) := sorry

end Module.LocalCohomology

end
