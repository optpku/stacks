module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.Affine
public import Mathlib.Algebra.Homology.LocalCohomology
public import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Local cohomology of affine punctured spectra

Local-cohomology and regular-sequence obstructions to affineness of punctured spectra.
-/

@[expose] public section

open AlgebraicGeometry IsLocalRing

universe u v

namespace AlgebraicGeometry.PuncturedSpectrum

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- If the punctured spectrum is affine, quotienting by a nonzerodivisor in the maximal ideal
does not give vanishing degree-zero local cohomology supported on a finitely generated ideal
with maximal radical. -/
theorem not_isZero_localCohomology_zero_quotient_of_isAffineOpen
    (hU : IsAffineOpen (puncturedOpen A)) {I : Ideal A} (hIfg : I.FG)
    (hI : maximalIdeal A = I.radical) {f : A} (hf_mem : f ∈ maximalIdeal A)
    (hf_nzd : f ∈ nonZeroDivisors A) :
    ¬ CategoryTheory.Limits.IsZero
      ((localCohomology I 0).obj (ModuleCat.of A (A ⧸ Ideal.span ({f} : Set A)))) := sorry

/-- The degree-zero local-cohomology obstruction persists over a local homomorphism whose
target maximal ideal is the radical of the extended source maximal ideal. -/
theorem not_isZero_localCohomology_zero_quotient_of_localHom
    (hU : IsAffineOpen (puncturedOpen A)) {I : Ideal A} (hIfg : I.FG)
    (hI : maximalIdeal A = I.radical) {A' : Type v} [CommRing A'] [IsLocalRing A']
    (φ : A →+* A') [IsLocalHom φ]
    (hφ : maximalIdeal A' = (Ideal.map φ (maximalIdeal A)).radical)
    {f : A'} (hf_mem : f ∈ maximalIdeal A') (hf_nzd : f ∈ nonZeroDivisors A') :
    ¬ CategoryTheory.Limits.IsZero ((localCohomology (Ideal.map φ I) 0).obj
      (ModuleCat.of A' (A' ⧸ Ideal.span ({f} : Set A')))) := sorry

/-- An affine punctured spectrum rules out regular sequences of length two in the local ring. -/
theorem not_isRegular_pair_of_isAffineOpen
    (hU : IsAffineOpen (puncturedOpen A)) :
    ∀ f g : A, ¬ RingTheory.Sequence.IsRegular A [f, g] := sorry

/-- A local target whose maximal ideal has the prescribed radical cannot contain a regular
sequence of length two when the source punctured spectrum is affine. -/
theorem not_isRegular_pair_of_localHom
    (hU : IsAffineOpen (puncturedOpen A)) {A' : Type v} [CommRing A'] [IsLocalRing A']
    (φ : A →+* A') [IsLocalHom φ]
    (hφ : maximalIdeal A' = (Ideal.map φ (maximalIdeal A)).radical) :
    ∀ f g : A', ¬ RingTheory.Sequence.IsRegular A' [f, g] := sorry

end AlgebraicGeometry.PuncturedSpectrum
