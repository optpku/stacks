/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.Tactic.CrossRefAttribute

/-!
# Chain Bounds from Finite Generation

@stack 0BBZ
-/

@[expose] public section

universe u

namespace PrimeSpectrum

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- If `q` is minimal over a prime `p` together with a finite set of generators, then every
strict chain from `p` to `q` has length at most the number of generators. -/
@[stacks 0BBZ "chain length over a finitely generated prime extension"]
theorem length_le_ncard_of_mem_minimalPrimes_sup_span
    {s : Set R} (hs : s.Finite) {p q : PrimeSpectrum R}
    (hq : q.asIdeal ∈ (p.asIdeal ⊔ Ideal.span s).minimalPrimes)
    (c : LTSeries (Set.Icc p q)) :
    c.length ≤ s.ncard := by
  let π : R →+* R ⧸ p.asIdeal := Ideal.Quotient.mk p.asIdeal
  let e : OrderIso (PrimeSpectrum (R ⧸ p.asIdeal)) (zeroLocus (p.asIdeal : Set R)) :=
    p.asIdeal.primeSpectrumQuotientOrderIsoZeroLocus
  let ψ : Set.Icc p q → PrimeSpectrum (R ⧸ p.asIdeal) := fun x ↦ e.symm ⟨x.1, x.2.1⟩
  have hψ : StrictMono ψ := fun _ _ h ↦ e.symm.strictMono h
  let sbar : Set (R ⧸ p.asIdeal) := π '' s
  let qbar : PrimeSpectrum (R ⧸ p.asIdeal) :=
    ⟨q.asIdeal.map π, Ideal.isPrime_map_quotientMk_of_isPrime (le_sup_left.trans hq.1.2)⟩
  have hspan_map : (Ideal.span s).map π = Ideal.span sbar := by
    rw [Ideal.map_span]
  have hqbar_min : qbar.asIdeal ∈ (Ideal.span sbar).minimalPrimes := by
    rw [← hspan_map]
    rw [Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective (Ideal.span s)]
    refine ⟨q.asIdeal, ?_, ?_⟩
    · simpa [π, Ideal.mk_ker, sup_comm] using hq
    · rfl
  have hqbar_ideal_height : qbar.asIdeal.height ≤ sbar.ncard :=
    Ideal.height_le_card_of_mem_minimalPrimes_span (hs.image π) hqbar_min
  have hqbar_order_height : Order.height qbar ≤ sbar.ncard := by
    simpa only [qbar.height_eq_orderHeight] using hqbar_ideal_height
  let cbar : LTSeries (PrimeSpectrum (R ⧸ p.asIdeal)) := c.map ψ hψ
  have hlength : cbar.length ≤ Order.height cbar.last := Order.length_le_height_last
  have hcbar_last : cbar.last ≤ qbar := by
    change ψ c.last ≤ e.symm ⟨q, le_sup_left.trans hq.1.2⟩
    exact e.symm.monotone c.last.2.2
  have hcard : sbar.ncard ≤ s.ncard := Set.ncard_image_le hs
  have hcard' : (sbar.ncard : ℕ∞) ≤ s.ncard := by
    exact_mod_cast hcard
  simpa [cbar] using
    hlength.trans ((Order.height_mono hcbar_last).trans (hqbar_order_height.trans hcard'))

end PrimeSpectrum
