/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.AdicComparison
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.Completion.Stabilization
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.AlgebraizationSituation
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.AlgebraizationSituation.EssentialConstancy
public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler
public import ReasLib.CategoryTheory.InverseSystem.Milnor.Derived.Canonical

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ModuleCat.SupportedOn Opposite

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.SupportedOn

variable {A : Type u} [CommRing A]

/-- An index simultaneously records the seven stabilization properties of an adic quotient tower. -/
def IsAdicStabilizationIndex
    (T : Set (PrimeSpectrum A)) (I : Ideal A) (M : ModuleCat.{u} A)
    (s : ℤ) (m : ℕ) : Prop :=
  (∀ i : ℤ, i ≤ s → ∀ n : ℕ, m ≤ n →
      Mono (adicComparison T I M i n)) ∧
    (∀ i : ℤ, i < s →
      SequentialInverseSystem.IsMittagLeffler (adicTower T I M i)) ∧
    (∀ i : ℤ, i ≤ s →
      SequentialInverseSystem.IsMittagLeffler (adicTailTower T I M m i)) ∧
    (∀ i : ℤ, i < s → IsIso (adicLimitComparison T I M i)) ∧
    IsIso (adicTailLimitComparison T I M m s) ∧
    (Mono (adicLimitComparison T I M s) ∧
      I ^ m ≤ Module.annihilator A
        ((cokernel (adicLimitComparison T I M s) : ModuleCat.{u} A) : Type u)) ∧
    I ^ m ≤ Module.annihilator A
      ((SequentialInverseSystem.Milnor.ProductCone.canonicalR1
        (adicTower T I M s) : ModuleCat.{u} A) : Type u)

namespace IsAdicStabilizationIndex

/-- An adic stabilization index gives eventual injectivity in every degree at most `s`. -/
theorem comparison_mono
    {T : Set (PrimeSpectrum A)} {I : Ideal A} {M : ModuleCat.{u} A}
    {s : ℤ} {m : ℕ} (h : IsAdicStabilizationIndex T I M s m) :
    ∀ i : ℤ, i ≤ s → ∀ n : ℕ, m ≤ n → Mono (adicComparison T I M i n) := sorry

/-- An adic stabilization index gives the Mittag-Leffler property for the ordinary quotient tower. -/
theorem quotient_isMittagLeffler
    {T : Set (PrimeSpectrum A)} {I : Ideal A} {M : ModuleCat.{u} A}
    {s : ℤ} {m : ℕ} (h : IsAdicStabilizationIndex T I M s m) :
    ∀ i : ℤ, i < s →
      SequentialInverseSystem.IsMittagLeffler (adicTower T I M i) := sorry

/-- An adic stabilization index gives the Mittag-Leffler property for the tail quotient tower. -/
theorem tail_isMittagLeffler
    {T : Set (PrimeSpectrum A)} {I : Ideal A} {M : ModuleCat.{u} A}
    {s : ℤ} {m : ℕ} (h : IsAdicStabilizationIndex T I M s m) :
    ∀ i : ℤ, i ≤ s →
      SequentialInverseSystem.IsMittagLeffler (adicTailTower T I M m i) := sorry

/-- An adic stabilization index makes the ordinary limit comparison invertible below degree `s`. -/
theorem limitComparison_isIso
    {T : Set (PrimeSpectrum A)} {I : Ideal A} {M : ModuleCat.{u} A}
    {s : ℤ} {m : ℕ} (h : IsAdicStabilizationIndex T I M s m) :
    ∀ i : ℤ, i < s → IsIso (adicLimitComparison T I M i) := sorry

/-- An adic stabilization index makes the degree-`s` tail limit comparison invertible. -/
theorem tailLimitComparison_isIso
    {T : Set (PrimeSpectrum A)} {I : Ideal A} {M : ModuleCat.{u} A}
    {s : ℤ} {m : ℕ} (h : IsAdicStabilizationIndex T I M s m) :
    IsIso (adicTailLimitComparison T I M m s) := sorry

/-- The degree-`s` ordinary comparison is mono and has cokernel annihilated by `I ^ m`. -/
theorem limitComparison_mono_and_cokernel
    {T : Set (PrimeSpectrum A)} {I : Ideal A} {M : ModuleCat.{u} A}
    {s : ℤ} {m : ℕ} (h : IsAdicStabilizationIndex T I M s m) :
    Mono (adicLimitComparison T I M s) ∧
      I ^ m ≤ Module.annihilator A
        ((cokernel (adicLimitComparison T I M s) : ModuleCat.{u} A) : Type u) := sorry

/-- The degree-`s` first derived limit is annihilated by `I ^ m`. -/
theorem firstDerivedLimit_annihilated
    {T : Set (PrimeSpectrum A)} {I : Ideal A} {M : ModuleCat.{u} A}
    {s : ℤ} {m : ℕ} (h : IsAdicStabilizationIndex T I M s m) :
    I ^ m ≤ Module.annihilator A
      ((SequentialInverseSystem.Milnor.ProductCone.canonicalR1
        (adicTower T I M s) : ModuleCat.{u} A) : Type u) := sorry

end IsAdicStabilizationIndex

end CategoryTheory.ModuleCat.SupportedOn

namespace Ideal.LocalCohomology.AlgebraizationSituation

variable {A : Type u} [CommRing A]

/-- Under an algebraization situation, one exponent controls all adic stabilization properties. -/
theorem existsAdicStabilizationIndex
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (I : Ideal A) (M : Type u)
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    (T : Set (PrimeSpectrum A)) (s d : ℤ)
    (h : AlgebraizationSituation H I M T s d) :
    ∃ m₀ : ℕ,
      CategoryTheory.ModuleCat.SupportedOn.IsAdicStabilizationIndex
        T I (ModuleCat.of A M) s m₀ := sorry

end Ideal.LocalCohomology.AlgebraizationSituation

namespace Ideal.LocalCohomology.AlgebraizationSituation

variable {A : Type u} [CommRing A]

/-- Under the algebraization hypotheses, sufficiently small supports have an
invertible canonical comparison with the inverse limit of the adic quotient
cohomology system. -/
theorem exists_stabilizingIdeal_limitComparison
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (I a : Ideal A) (hIa : I ≤ a) [IsAdicComplete I A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (s d : ℤ)
    (hSituation : AlgebraizationSituation H I M
      (PrimeSpectrum.zeroLocus (a : Set A)) s d)
    (δ : PrimeSpectrum A → ℤ) [IsDimensionFunction δ]
    (δmax δmin : ℤ)
    (hδmax : IsGreatest
      (δ '' (PrimeSpectrum.zeroLocus (a : Set A) ∩
        PrimeSpectrum.zeroLocus (I : Set A))) δmax)
    (hδmin : IsLeast
      (δ '' (PrimeSpectrum.zeroLocus (a : Set A) ∩
        PrimeSpectrum.zeroLocus (I : Set A))) δmin)
    (h_depth : ∀ p : PrimeSpectrum A,
      p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
        p ∉ PrimeSpectrum.associatedSubset I a →
          ((s + 1 : ℤ) : EInt) ≤
              ((WithTop.map Int.ofNat
                (moduleDepth (Localization.AtPrime p.asIdeal)
                  (LocalizedModule.AtPrime p.asIdeal M)) : WithTop ℤ) : EInt) ∨
            ∀ q : PrimeSpectrum A,
              q ∈ (PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
                PrimeSpectrum.zeroLocus (a : Set A)) ∩
                  PrimeSpectrum.zeroLocus (I : Set A) →
                ((d + (s + 1 : ℤ)) : EInt) <
                  ((WithTop.map Int.ofNat
                    (moduleDepth (Localization.AtPrime p.asIdeal)
                      (LocalizedModule.AtPrime p.asIdeal M)) : WithTop ℤ) : EInt) +
                    WithBot.map (WithTop.map Int.ofNat)
                      (ringKrullDim (p.asIdeal.quotientAtPrime q)))
    (h_exceptional : ∀ p : PrimeSpectrum A,
      p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
        p ∉ PrimeSpectrum.associatedSubset I a →
        Set.Nonempty
          ((PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
              PrimeSpectrum.zeroLocus (a : Set A)) ∩
            PrimeSpectrum.zeroLocus (I : Set A)) →
        ((WithTop.map Int.ofNat
          (moduleDepth (Localization.AtPrime p.asIdeal)
            (LocalizedModule.AtPrime p.asIdeal M)) : WithTop ℤ) : EInt) <
          ((s + 1 : ℤ) : EInt) →
          (WithBot.map (WithTop.map Int.ofNat)
              (Module.supportDim (Localization.AtPrime p.asIdeal)
                (LocalizedModule.AtPrime p.asIdeal M)) < ((s + 3 : ℤ) : EInt)) ∨
            δ p > d + δmax - 1 ∨
              ∀ q : PrimeSpectrum A,
                q ∈ (PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
                  PrimeSpectrum.zeroLocus (a : Set A)) ∩
                    PrimeSpectrum.zeroLocus (I : Set A) →
                  ((WithTop.map Int.ofNat
                    (moduleDepth (Localization.AtPrime p.asIdeal)
                      (LocalizedModule.AtPrime p.asIdeal M)) : WithTop ℤ) : EInt) +
                      WithBot.map (WithTop.map Int.ofNat)
                        (ringKrullDim (p.asIdeal.quotientAtPrime q)) >
                    ((d + (s + 1 : ℤ) + δmax - δmin - 2 : ℤ) : EInt)) :
    ∃ J₀ : Ideal A, ∃ hJ₀ : J₀ ≤ a,
      PrimeSpectrum.zeroLocus (J₀ : Set A) ∩
          PrimeSpectrum.zeroLocus (I : Set A) =
        PrimeSpectrum.zeroLocus (a : Set A) ∩
          PrimeSpectrum.zeroLocus (I : Set A) ∧
      ∀ (J : Ideal A) (hJ : J ≤ J₀),
        (hV : PrimeSpectrum.zeroLocus (J : Set A) ∩
            PrimeSpectrum.zeroLocus (I : Set A) =
          PrimeSpectrum.zeroLocus (a : Set A) ∩
            PrimeSpectrum.zeroLocus (I : Set A)) →
          IsIso (CategoryTheory.ModuleCat.SupportedOn.adicSupportLimitComparison
            I a J (hJ.trans hJ₀) hV (ModuleCat.of A M) (s + 1)) := sorry

end Ideal.LocalCohomology.AlgebraizationSituation
