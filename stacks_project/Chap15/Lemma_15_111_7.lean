module

import StacksCheckRecall
public import ReasLib.RingTheory.Invariant.FixedPoints.TensorProduct
public import ReasLib.RingTheory.Invariant.TensorProduct.Flat
public import ReasLib.RingTheory.Invariant.TensorProduct.ShiftPower
public import ReasLib.RingTheory.RingHom.ShiftPower.Spectrum

/-!
# Lemma 15.111.7

@stack 0BRH
-/

@[expose] public section

open FixedPoints.Tensor
open scoped Algebra.TensorProduct.RightAction

universe u v w

/-
Lemma 15.111.7 (current Stacks numbering: Lemma 15.112.7, tag `0BRH`): Let `G` be a finite
group acting on a commutative ring `R`, let `A` be a commutative algebra over `R^G`, and write
`A ⊗[R^G] R` for the base change with its right-factor action.  The canonical map
`A ⟶ (A ⊗[R^G] R)^G` is an isomorphism when `R^G ⟶ A` is flat; it is integral in general; it
induces a homeomorphism on prime spectra; and it induces purely inseparable residue-field maps.

The source-facing map is `FixedPoints.Tensor.fixedPointsMap`.  The four conclusions use the
generic tensor and shift-power owners directly, so downstream files can import those owners
without depending on this chapter file.
-/

section

variable {R : Type u} {G : Type v} {A : Type w}
variable [CommRing R] [Group G] [Finite G] [MulSemiringAction G R]
variable [CommRing A] [Algebra (FixedPoints.subring R G) A]

section

variable [Module.Flat (FixedPoints.subring R G) A]

/- Lemma 15.111.7 (1): flatness identifies the canonical map with the fixed tensor equalizer. -/
@[stacks 0BRH "flat fixed-point tensor map is bijective"]
#check (Algebra.IsInvariant.TensorProduct.toFixed_bijective_of_flat
  (S := FixedPoints.subring R G) (A := A) (B := R) (G := G) :
  Function.Bijective (fixedPointsMap (R := R) (G := G) (A := A)).toRingHom)

end

/- Lemma 15.111.7 (2): the canonical fixed-point tensor map is integral. -/
@[stacks 0BRH "fixed-point tensor map is integral"]
#check (Algebra.IsInvariant.TensorProduct.isIntegral
  (S := FixedPoints.subring R G) (A := A) (B := R) (G := G) :
  (fixedPointsMap (R := R) (G := G) (A := A)).toRingHom.IsIntegral)

/- Lemma 15.111.7 (3): the induced map on prime spectra is a homeomorphism. -/
@[stacks 0BRH "fixed-point tensor spectrum is a homeomorphism"]
#check (RingHom.IsPowerSurjective.isHomeomorph_comap
  (RingHom.ShiftPower.isPowerSurjective
    (fixedPointsMap (R := R) (G := G) (A := A)).toRingHom
    (Algebra.IsInvariant.TensorProduct.isGenerated
      (S := FixedPoints.subring R G) (A := A) (B := R) (G := G)))
  (Algebra.IsInvariant.TensorProduct.ker_isLocallyNilpotent
    (S := FixedPoints.subring R G) (A := A) (B := R) (G := G)) :
  IsHomeomorph (PrimeSpectrum.comap
    (fixedPointsMap (R := R) (G := G) (A := A)).toRingHom))

/- Lemma 15.111.7 (4): residue-field maps induced by the canonical map are purely inseparable. -/
@[stacks 0BRH "fixed-point tensor residue fields are purely inseparable"]
#check (RingHom.ShiftPower.Spectrum.residueField_isPurelyInseparable
  (fixedPointsMap (R := R) (G := G) (A := A)).toRingHom
  (Algebra.IsInvariant.TensorProduct.isGenerated
    (S := FixedPoints.subring R G) (A := A) (B := R) (G := G)) :
  RingHom.ResidueField.MapsPurelyInseparable
    (fixedPointsMap (R := R) (G := G) (A := A)).toRingHom)

end
