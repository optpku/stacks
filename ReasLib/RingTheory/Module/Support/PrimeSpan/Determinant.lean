/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.FiniteLength.Determinant
public import ReasLib.RingTheory.Module.Support.PrimeSpan
public import Mathlib.RingTheory.Localization.Module

@[expose] public section

noncomputable section

universe u v w

namespace Module.PrimeSpan

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- A finite prime-span filtration gives finite length after localization at that prime. -/
theorem localizedIsFiniteLength (q : PrimeSpectrum R) {l : ℕ} (z : Fin l → M)
    (h_span : Submodule.span R (Set.range z) = ⊤)
    (h_factors : ∀ i : Fin l,
      Nonempty
        ((Submodule.span R (z '' Set.Iic i) ⧸
            (Submodule.span R (z '' Set.Iio i)).submoduleOf
              (Submodule.span R (z '' Set.Iic i))) ≃ₗ[R]
          R ⧸ q.asIdeal)) :
    IsFiniteLength (Localization.AtPrime q.asIdeal)
      (LocalizedModule.AtPrime q.asIdeal M) := sorry

/-- The localized length attached to a prime-span filtration is its number of factors. -/
theorem localizedLength_eq (q : PrimeSpectrum R) {l : ℕ} (z : Fin l → M)
    (h_span : Submodule.span R (Set.range z) = ⊤)
    (h_factors : ∀ i : Fin l,
      Nonempty
        ((Submodule.span R (z '' Set.Iic i) ⧸
            (Submodule.span R (z '' Set.Iio i)).submoduleOf
              (Submodule.span R (z '' Set.Iic i))) ≃ₗ[R]
          R ⧸ q.asIdeal)) :
    FiniteLengthDeterminant.length (Localization.AtPrime q.asIdeal)
        (LocalizedModule.AtPrime q.asIdeal M)
        (localizedIsFiniteLength q z h_span h_factors) = l := sorry

/-- The localized generators of a prime-span filtration form an admissible determinant family. -/
theorem localizedFamily_isAdmissible (q : PrimeSpectrum R) {l : ℕ} (z : Fin l → M)
    (h_span : Submodule.span R (Set.range z) = ⊤)
    (h_factors : ∀ i : Fin l,
      Nonempty
        ((Submodule.span R (z '' Set.Iic i) ⧸
            (Submodule.span R (z '' Set.Iio i)).submoduleOf
              (Submodule.span R (z '' Set.Iic i))) ≃ₗ[R]
          R ⧸ q.asIdeal)) :
    FiniteLengthDeterminant.IsAdmissible
      (Localization.AtPrime q.asIdeal) (LocalizedModule.AtPrime q.asIdeal M)
      (localizedIsFiniteLength q z h_span h_factors)
      (fun i ↦ LocalizedModule.mkLinearMap q.asIdeal.primeCompl M
        (z (Fin.cast (localizedLength_eq q z h_span h_factors) i))) := sorry

/-- The determinant symbol represented by the localized generators of a prime-span filtration. -/
noncomputable def symbol (q : PrimeSpectrum R) {l : ℕ} (z : Fin l → M)
    (h_span : Submodule.span R (Set.range z) = ⊤)
    (h_factors : ∀ i : Fin l,
      Nonempty
        ((Submodule.span R (z '' Set.Iic i) ⧸
            (Submodule.span R (z '' Set.Iio i)).submoduleOf
              (Submodule.span R (z '' Set.Iic i))) ≃ₗ[R]
          R ⧸ q.asIdeal)) :
    Module.FiniteLengthDeterminant (Localization.AtPrime q.asIdeal)
      (LocalizedModule.AtPrime q.asIdeal M)
      (localizedIsFiniteLength q z h_span h_factors) :=
  FiniteLengthDeterminant.symbol (Localization.AtPrime q.asIdeal)
    (LocalizedModule.AtPrime q.asIdeal M)
    (localizedIsFiniteLength q z h_span h_factors)
    ⟨fun i ↦ LocalizedModule.mkLinearMap q.asIdeal.primeCompl M
        (z (Fin.cast (localizedLength_eq q z h_span h_factors) i)),
      localizedFamily_isAdmissible q z h_span h_factors⟩

/-- `symbol` is the determinant class of the explicitly localized and reindexed family. -/
theorem symbol_def (q : PrimeSpectrum R) {l : ℕ} (z : Fin l → M)
    (h_span : Submodule.span R (Set.range z) = ⊤)
    (h_factors : ∀ i : Fin l,
      Nonempty
        ((Submodule.span R (z '' Set.Iic i) ⧸
            (Submodule.span R (z '' Set.Iio i)).submoduleOf
              (Submodule.span R (z '' Set.Iic i))) ≃ₗ[R]
          R ⧸ q.asIdeal)) :
    symbol q z h_span h_factors =
      FiniteLengthDeterminant.symbol (Localization.AtPrime q.asIdeal)
        (LocalizedModule.AtPrime q.asIdeal M)
        (localizedIsFiniteLength q z h_span h_factors)
        ⟨fun i ↦ LocalizedModule.mkLinearMap q.asIdeal.primeCompl M
            (z (Fin.cast (localizedLength_eq q z h_span h_factors) i)),
          localizedFamily_isAdmissible q z h_span h_factors⟩ := sorry

/-- Mapping the localized generators of a prime-span filtration gives an admissible family in
the target determinant. -/
theorem mappedFamily_isAdmissible (q : PrimeSpectrum R) {l : ℕ}
    (φ : M →ₗ[R] N) (x : Fin l → M) (y : Fin l → N)
    (hx_span : Submodule.span R (Set.range x) = ⊤)
    (hx_factors : ∀ i : Fin l,
      Nonempty
        ((Submodule.span R (x '' Set.Iic i) ⧸
            (Submodule.span R (x '' Set.Iio i)).submoduleOf
              (Submodule.span R (x '' Set.Iic i))) ≃ₗ[R]
          R ⧸ q.asIdeal))
    (hy_span : Submodule.span R (Set.range y) = ⊤)
    (hy_factors : ∀ i : Fin l,
      Nonempty
        ((Submodule.span R (y '' Set.Iic i) ⧸
            (Submodule.span R (y '' Set.Iio i)).submoduleOf
              (Submodule.span R (y '' Set.Iic i))) ≃ₗ[R]
          R ⧸ q.asIdeal)) :
    FiniteLengthDeterminant.IsAdmissible
      (Localization.AtPrime q.asIdeal) (LocalizedModule.AtPrime q.asIdeal N)
      (localizedIsFiniteLength q y hy_span hy_factors)
      (fun i ↦ LocalizedModule.map q.asIdeal.primeCompl φ
        (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M
          (x (Fin.cast (localizedLength_eq q y hy_span hy_factors) i)))) := sorry

/-- The target determinant symbol represented by the localized images of a source
prime-span family. -/
noncomputable def mapSymbol (q : PrimeSpectrum R) {l : ℕ}
    (φ : M →ₗ[R] N) (x : Fin l → M) (y : Fin l → N)
    (hx_span : Submodule.span R (Set.range x) = ⊤)
    (hx_factors : ∀ i : Fin l,
      Nonempty
        ((Submodule.span R (x '' Set.Iic i) ⧸
            (Submodule.span R (x '' Set.Iio i)).submoduleOf
              (Submodule.span R (x '' Set.Iic i))) ≃ₗ[R]
          R ⧸ q.asIdeal))
    (hy_span : Submodule.span R (Set.range y) = ⊤)
    (hy_factors : ∀ i : Fin l,
      Nonempty
        ((Submodule.span R (y '' Set.Iic i) ⧸
            (Submodule.span R (y '' Set.Iio i)).submoduleOf
              (Submodule.span R (y '' Set.Iic i))) ≃ₗ[R]
          R ⧸ q.asIdeal)) :
    Module.FiniteLengthDeterminant (Localization.AtPrime q.asIdeal)
      (LocalizedModule.AtPrime q.asIdeal N)
      (localizedIsFiniteLength q y hy_span hy_factors) :=
  FiniteLengthDeterminant.symbol (Localization.AtPrime q.asIdeal)
    (LocalizedModule.AtPrime q.asIdeal N)
    (localizedIsFiniteLength q y hy_span hy_factors)
    ⟨fun i ↦ LocalizedModule.map q.asIdeal.primeCompl φ
        (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M
          (x (Fin.cast (localizedLength_eq q y hy_span hy_factors) i))),
      mappedFamily_isAdmissible q φ x y hx_span hx_factors hy_span hy_factors⟩

/-- `mapSymbol` is the determinant class of the explicitly localized image family. -/
theorem mapSymbol_def (q : PrimeSpectrum R) {l : ℕ}
    (φ : M →ₗ[R] N) (x : Fin l → M) (y : Fin l → N)
    (hx_span : Submodule.span R (Set.range x) = ⊤)
    (hx_factors : ∀ i : Fin l,
      Nonempty
        ((Submodule.span R (x '' Set.Iic i) ⧸
            (Submodule.span R (x '' Set.Iio i)).submoduleOf
              (Submodule.span R (x '' Set.Iic i))) ≃ₗ[R]
          R ⧸ q.asIdeal))
    (hy_span : Submodule.span R (Set.range y) = ⊤)
    (hy_factors : ∀ i : Fin l,
      Nonempty
        ((Submodule.span R (y '' Set.Iic i) ⧸
            (Submodule.span R (y '' Set.Iio i)).submoduleOf
              (Submodule.span R (y '' Set.Iic i))) ≃ₗ[R]
          R ⧸ q.asIdeal)) :
    mapSymbol q φ x y hx_span hx_factors hy_span hy_factors =
      FiniteLengthDeterminant.symbol (Localization.AtPrime q.asIdeal)
        (LocalizedModule.AtPrime q.asIdeal N)
        (localizedIsFiniteLength q y hy_span hy_factors)
        ⟨fun i ↦ LocalizedModule.map q.asIdeal.primeCompl φ
            (LocalizedModule.mkLinearMap q.asIdeal.primeCompl M
              (x (Fin.cast (localizedLength_eq q y hy_span hy_factors) i))),
          mappedFamily_isAdmissible q φ x y hx_span hx_factors hy_span hy_factors⟩ := sorry

end Module.PrimeSpan
