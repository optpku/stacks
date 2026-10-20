module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.KrullDimension.Basic

/-!
# Affine punctured spectra

Criteria for the punctured spectrum of a local ring to be affine, and the dimension
characterization in the Noetherian case.
-/

@[expose] public section

open AlgebraicGeometry IsLocalRing

universe u v

namespace AlgebraicGeometry.PuncturedSpectrum

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- If the punctured spectrum of a local ring is affine, its maximal ideal is the radical of
a finitely generated ideal. -/
theorem exists_fg_maximalIdeal_eq_radical_of_isAffineOpen
    (hU : IsAffineOpen (puncturedOpen A)) :
    ∃ I : Ideal A, I.FG ∧ maximalIdeal A = I.radical := sorry

/-- If the maximal ideal of a local ring is the radical of a principal ideal, then its
punctured spectrum is affine. -/
theorem isAffineOpen_of_maximalIdeal_eq_radical_span_singleton
    {f : A} (hf : maximalIdeal A = (Ideal.span ({f} : Set A)).radical) :
    IsAffineOpen (puncturedOpen A) := sorry

/-- Affineness of the punctured spectrum is preserved by a local ring homomorphism when the
target maximal ideal is the radical of the extended source maximal ideal. -/
theorem isAffineOpen_of_isAffineOpen_of_localHom
    (hU : IsAffineOpen (puncturedOpen A)) {A' : Type v} [CommRing A'] [IsLocalRing A']
    (φ : A →+* A') [IsLocalHom φ]
    (hφ : maximalIdeal A' = (Ideal.map φ (maximalIdeal A)).radical) :
    IsAffineOpen (puncturedOpen A') := sorry

variable [IsNoetherianRing A]

/-- The punctured spectrum of a Noetherian local ring is affine exactly when the ring has
Krull dimension at most one. -/
theorem isAffineOpen_iff_krullDimLE_one :
    IsAffineOpen (puncturedOpen A) ↔ Ring.KrullDimLE 1 A := sorry

/-- The punctured spectrum of a Noetherian local ring is affine exactly when its numerical
Krull dimension is at most one. -/
theorem isAffineOpen_iff_ringKrullDim_le_one :
    IsAffineOpen (puncturedOpen A) ↔ ringKrullDim A ≤ 1 := by
  rw [isAffineOpen_iff_krullDimLE_one]
  simpa using (Ring.krullDimLE_iff (R := A) (n := 1))

/-- The punctured spectrum of a Noetherian local ring of Krull dimension at least two is not
affine. -/
theorem not_isAffineOpen_of_two_le_ringKrullDim (hdim : 2 ≤ ringKrullDim A) :
    ¬ IsAffineOpen (puncturedOpen A) := sorry

end AlgebraicGeometry.PuncturedSpectrum
