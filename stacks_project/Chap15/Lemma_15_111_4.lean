/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Invariant.FixedPoints.IdealQuotient.Spectrum

/-!
# Lemma 15.111.4

@stack 0H35
-/

@[expose] public section

universe u v

open Polynomial

/- Lemma 15.111.4 (current Stacks section: Lemma 15.112.4, tag `0H35`):
for a finite group acting on a commutative ring `R` and an ideal `J` of `FixedPoints.subring R G`,
the canonical map `FixedPoints.subring R G ⧸ J →
FixedPoints.subring (R ⧸ FixedPoints.Quotient.ideal J) G` has the monic-polynomial and kernel-power
properties below; consequently it is integral, induces a homeomorphism on spectra, and has
purely inseparable residue fields. The shared owner uses `FixedPoints.Quotient` so the quotient
action is explicit and reusable.
-/

/- Lemma 15.111.4 (1): the monic polynomial clause. -/
@[stacks 0H35 "Lemma 15.111.4 (1)"]
#check fun (R : Type u) (G : Type v) [CommRing R] [Group G]
    [MulSemiringAction G R] [Finite G]
    (J : Ideal (FixedPoints.subring R G))
    (b : FixedPoints.Quotient.fixed J) ↦
  (FixedPoints.Quotient.exists_monic J b :
    ∃ P : Polynomial (FixedPoints.subring R G ⧸ J),
      P.Monic ∧
        P.map (FixedPoints.Quotient.map J) =
          (X - C b) ^ Nat.card G)

/- Lemma 15.111.4 (2): the kernel power clause. -/
@[stacks 0H35 "Lemma 15.111.4 (2)"]
#check fun (R : Type u) (G : Type v) [CommRing R] [Group G]
    [MulSemiringAction G R] [Finite G]
    (J : Ideal (FixedPoints.subring R G))
    (a : RingHom.ker (FixedPoints.Quotient.map J)) ↦
  (FixedPoints.Quotient.kernel_pow J a :
    (X - C a.1) ^ Nat.card G = X ^ Nat.card G)

/- Lemma 15.111.4 (3): integrality. -/
@[stacks 0H35 "Lemma 15.111.4 (3)"]
#check fun (R : Type u) (G : Type v) [CommRing R] [Group G]
    [MulSemiringAction G R] [Finite G]
    (J : Ideal (FixedPoints.subring R G)) ↦
  (FixedPoints.Quotient.isIntegral J :
    (FixedPoints.Quotient.map J).IsIntegral)

/- Lemma 15.111.4 (4): the spectrum homeomorphism. -/
@[stacks 0H35 "Lemma 15.111.4 (4)"]
#check fun (R : Type u) (G : Type v) [CommRing R] [Group G]
    [MulSemiringAction G R] [Finite G]
    (J : Ideal (FixedPoints.subring R G)) ↦
  (FixedPoints.Quotient.isHomeomorph J :
    IsHomeomorph (PrimeSpectrum.comap (FixedPoints.Quotient.map J)))

/- Lemma 15.111.4 (5): purely inseparable residue fields. -/
@[stacks 0H35 "Lemma 15.111.4 (5)"]
#check fun (R : Type u) (G : Type v) [CommRing R] [Group G]
    [MulSemiringAction G R] [Finite G]
    (J : Ideal (FixedPoints.subring R G)) ↦
  (FixedPoints.Quotient.residueField_isPurelyInseparable J :
    RingHom.ResidueField.MapsPurelyInseparable (FixedPoints.Quotient.map J))
