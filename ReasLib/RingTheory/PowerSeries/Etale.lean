module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Data.Complex.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.RingHom.Etale

@[expose] public section

universe u

noncomputable section

namespace PowerSeries

/-- The ideal imposing the relation `T ^ n = X` in the Laurent polynomial ring over
`PowerSeries ℂ`. -/
def kummerIdeal (n : ℕ) :
    Ideal (LaurentPolynomial (PowerSeries ℂ)) :=
  Ideal.span {LaurentPolynomial.T (1 : ℤ) ^ n -
    LaurentPolynomial.C (PowerSeries.X : PowerSeries ℂ)}

/-- The Laurent Kummer factor obtained by imposing `T ^ n = X`. -/
abbrev kummerFactor (n : ℕ) : Type :=
  LaurentPolynomial (PowerSeries ℂ) ⧸ kummerIdeal n

/-- The canonical map from `PowerSeries ℂ` to its `n`th Laurent Kummer factor. -/
def kummerMap (n : ℕ) :
    PowerSeries ℂ →+* kummerFactor n :=
  (Ideal.Quotient.mk (kummerIdeal n)).comp
    (LaurentPolynomial.C : PowerSeries ℂ →+* LaurentPolynomial (PowerSeries ℂ))

/-- The base map into a finite product of trivial and Laurent Kummer factors. -/
def productMap {I₀ I₁ : Type u} (n : I₁ → ℕ) :
    PowerSeries ℂ →+*
      ((I₀ → PowerSeries ℂ) × (∀ i, kummerFactor (n i))) :=
  (RingHom.pi (fun _ : I₀ ↦ RingHom.id (PowerSeries ℂ))).prod
    (RingHom.pi (fun i ↦ kummerMap (n i)))

/-- Every étale `PowerSeries ℂ`-algebra is a finite product of trivial factors and
Laurent Kummer factors, with the displayed product decomposition preserving the
base map. -/
theorem etaleProductDecomposition
    {S : Type u} [CommRing S] (f : PowerSeries ℂ →+* S) (hf : f.Etale) :
    ∃ (I₀ I₁ : Type u) (_ : Fintype I₀) (_ : Fintype I₁)
      (n : I₁ → ℕ) (h_n : ∀ i, 0 < n i) (e : S ≃+*
        ((I₀ → PowerSeries ℂ) × (∀ i, kummerFactor (n i)))),
      e.toRingHom.comp f = productMap n := sorry

/-- Each Laurent Kummer factor factors through localization at `X`, corresponding
to the open `D(X)` in the spectrum of `PowerSeries ℂ`. -/
theorem kummerFactorsThroughDt (n : ℕ) (hn : 0 < n) :
    ∃ g : Localization.Away (PowerSeries.X : PowerSeries ℂ) →+*
      kummerFactor n,
      g.comp (algebraMap (PowerSeries ℂ)
        (Localization.Away (PowerSeries.X : PowerSeries ℂ))) =
        kummerMap n := sorry

end PowerSeries
