module

import StacksCheckRecall
public import ReasLib.RingTheory.Invariant.Quotient.Spectrum

/-!
@stack 09EG
-/

@[expose] public section

open PrimeSpectrum
open scoped Pointwise

universe u v

/- Lemma 15.111.2 (current Stacks numbering: Lemma 15.112.2, tag `09EG`):
if a finite group acts on a commutative ring and stabilizes an ideal `I`, then
the canonical map `R^G / (I ∩ R^G) → (R / I)^G` is integral, its spectrum map is a
homeomorphism, and its residue-field extensions are purely inseparable. -/
@[stacks 09EG "Lemma 15.111.2"]
#check fun (R : Type u) (G : Type v) [CommRing R] [Group G]
    [MulSemiringAction G R] [Finite G] (I : Ideal R)
    (hI : ∀ g : G, g • I = I) ↦
  (Ideal.Quotient.FixedPoints.map_spec I hI :
    (Ideal.Quotient.fixedPointsMap I hI).IsIntegral ∧
      IsHomeomorph (PrimeSpectrum.comap (Ideal.Quotient.fixedPointsMap I hI)) ∧
      RingHom.ResidueField.MapsPurelyInseparable
        (Ideal.Quotient.fixedPointsMap I hI))
