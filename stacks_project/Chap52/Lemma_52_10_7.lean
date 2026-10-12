/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.IdealPower.Quotient.Sequential
public import ReasLib.Algebra.Category.ModuleCat.SupportedOn.AdicComparison
public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.AlgebraizationSituation.Stabilization
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ModuleCat.SupportedOn Opposite

noncomputable section

universe u

namespace Ideal.LocalCohomology.AlgebraizationSituation

variable {A : Type u} [CommRing A]

/-- The source-facing name for the exact ideal-power quotient system. -/
noncomputable abbrev adicQuotientSystem
    (I : Ideal A) (M : ModuleCat.{u} A) :
    SequentialInverseSystem (ModuleCat.{u} A) :=
  Ideal.PowerQuotient.system I M

/-- The source-facing name for the cone of exact quotient comparisons. -/
noncomputable abbrev cohomologyComparisonCone
    (T : Set (PrimeSpectrum A)) (I : Ideal A) (M : ModuleCat.{u} A)
    (i : ℤ) : Cone (supportedCohomologyTower T (adicQuotientSystem I M) i) :=
  CategoryTheory.ModuleCat.SupportedOn.adicComparisonCone T I M i

/-- The source-facing name for the exact quotient limit comparison. -/
noncomputable abbrev cohomologyLimitComparison
    (T : Set (PrimeSpectrum A)) (I : Ideal A) (M : ModuleCat.{u} A)
    (i : ℤ) :
    cohomology T (ModuleCat.single0Functor.obj M) i ⟶
      limit (supportedCohomologyTower T (adicQuotientSystem I M) i) :=
  CategoryTheory.ModuleCat.SupportedOn.adicLimitComparison T I M i

end Ideal.LocalCohomology.AlgebraizationSituation

/- Lemma 52.10.7 -/
@[stacks 0EFY] #check
  (Ideal.LocalCohomology.AlgebraizationSituation.existsAdicStabilizationIndex :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
      (I : Ideal A) (M : Type u)
      [AddCommGroup M] [Module A M] [Module.Finite A M]
      (T : Set (PrimeSpectrum A)) (s d : ℤ)
      (h : Ideal.LocalCohomology.AlgebraizationSituation H I M T s d),
      ∃ m₀ : ℕ,
        CategoryTheory.ModuleCat.SupportedOn.IsAdicStabilizationIndex
          T I (ModuleCat.of A M) s m₀)

/- Lemma 52.10.7 (1) -/
@[stacks 0EFY] #check
  (CategoryTheory.ModuleCat.SupportedOn.IsAdicStabilizationIndex.comparison_mono :
    ∀ {A : Type u} [CommRing A]
      {T : Set (PrimeSpectrum A)} {I : Ideal A} {M : ModuleCat.{u} A}
      {s : ℤ} {m : ℕ},
      CategoryTheory.ModuleCat.SupportedOn.IsAdicStabilizationIndex T I M s m →
        ∀ i : ℤ, i ≤ s → ∀ n : ℕ, m ≤ n →
          Mono (CategoryTheory.ModuleCat.SupportedOn.adicComparison T I M i n))

/- Lemma 52.10.7 (2) -/
@[stacks 0EFY] #check
  (CategoryTheory.ModuleCat.SupportedOn.IsAdicStabilizationIndex.quotient_isMittagLeffler :
    ∀ {A : Type u} [CommRing A]
      {T : Set (PrimeSpectrum A)} {I : Ideal A} {M : ModuleCat.{u} A}
      {s : ℤ} {m : ℕ},
      CategoryTheory.ModuleCat.SupportedOn.IsAdicStabilizationIndex T I M s m →
        ∀ i : ℤ, i < s →
          SequentialInverseSystem.IsMittagLeffler
            (CategoryTheory.ModuleCat.SupportedOn.adicTower T I M i))

/- Lemma 52.10.7 (3) -/
@[stacks 0EFY] #check
  (CategoryTheory.ModuleCat.SupportedOn.IsAdicStabilizationIndex.tail_isMittagLeffler :
    ∀ {A : Type u} [CommRing A]
      {T : Set (PrimeSpectrum A)} {I : Ideal A} {M : ModuleCat.{u} A}
      {s : ℤ} {m : ℕ},
      CategoryTheory.ModuleCat.SupportedOn.IsAdicStabilizationIndex T I M s m →
        ∀ i : ℤ, i ≤ s →
          SequentialInverseSystem.IsMittagLeffler
            (CategoryTheory.ModuleCat.SupportedOn.adicTailTower T I M m i))

/- Lemma 52.10.7 (4) -/
@[stacks 0EFY] #check
  (CategoryTheory.ModuleCat.SupportedOn.IsAdicStabilizationIndex.limitComparison_isIso :
    ∀ {A : Type u} [CommRing A]
      {T : Set (PrimeSpectrum A)} {I : Ideal A} {M : ModuleCat.{u} A}
      {s : ℤ} {m : ℕ},
      CategoryTheory.ModuleCat.SupportedOn.IsAdicStabilizationIndex T I M s m →
        ∀ i : ℤ, i < s →
          IsIso (CategoryTheory.ModuleCat.SupportedOn.adicLimitComparison T I M i))

/- Lemma 52.10.7 (5) -/
@[stacks 0EFY] #check
  (CategoryTheory.ModuleCat.SupportedOn.IsAdicStabilizationIndex.tailLimitComparison_isIso :
    ∀ {A : Type u} [CommRing A]
      {T : Set (PrimeSpectrum A)} {I : Ideal A} {M : ModuleCat.{u} A}
      {s : ℤ} {m : ℕ},
      CategoryTheory.ModuleCat.SupportedOn.IsAdicStabilizationIndex T I M s m →
        IsIso (CategoryTheory.ModuleCat.SupportedOn.adicTailLimitComparison T I M m s))

/- Lemma 52.10.7 (6) -/
@[stacks 0EFY] #check
  (CategoryTheory.ModuleCat.SupportedOn.IsAdicStabilizationIndex.limitComparison_mono_and_cokernel :
    ∀ {A : Type u} [CommRing A]
      {T : Set (PrimeSpectrum A)} {I : Ideal A} {M : ModuleCat.{u} A}
      {s : ℤ} {m : ℕ},
      CategoryTheory.ModuleCat.SupportedOn.IsAdicStabilizationIndex T I M s m →
        Mono (CategoryTheory.ModuleCat.SupportedOn.adicLimitComparison T I M s) ∧
          I ^ m ≤ Module.annihilator A
            ((cokernel (CategoryTheory.ModuleCat.SupportedOn.adicLimitComparison T I M s) :
              ModuleCat.{u} A) : Type u))

/- Lemma 52.10.7 (7) -/
@[stacks 0EFY] #check
  (CategoryTheory.ModuleCat.SupportedOn.IsAdicStabilizationIndex.firstDerivedLimit_annihilated :
    ∀ {A : Type u} [CommRing A]
      {T : Set (PrimeSpectrum A)} {I : Ideal A} {M : ModuleCat.{u} A}
      {s : ℤ} {m : ℕ},
      CategoryTheory.ModuleCat.SupportedOn.IsAdicStabilizationIndex T I M s m →
        I ^ m ≤ Module.annihilator A
          ((SequentialInverseSystem.Milnor.ProductCone.canonicalR1
            (CategoryTheory.ModuleCat.SupportedOn.adicTower T I M s) :
              ModuleCat.{u} A) : Type u))

end
