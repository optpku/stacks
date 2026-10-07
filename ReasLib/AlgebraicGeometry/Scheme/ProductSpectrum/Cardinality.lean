module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.SetTheory.Cardinal.Finite

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.ProductSpectrum

/-- The spectrum of a product of `n` copies of a field has exactly `n` points. -/
theorem card_fin (n : ℕ) (k : Type u) [Field k] :
    Nat.card (Spec (.of (Fin n → k))) = n := sorry

end AlgebraicGeometry.Scheme.ProductSpectrum
