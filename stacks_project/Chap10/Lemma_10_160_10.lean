/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Completion.RegularPresentation
import StacksCheckRecall

@[expose] public section

universe u v

open IsLocalRing

/-!
# Lemma 10.160.10

The two equal-characteristic power-series presentations are recalled from the
regular-local owner.

@stack 0C0S
-/

section

variable {R : Type u} [CommRing R] [IsCompleteLocalRing R] [IsRegularLocalRing R]

/- Lemma 10.160.10 (1), tag `0C0S`: in equal characteristic, a complete regular local ring is a
finite-variable formal power-series ring over its residue field. -/
@[stacks 0C0S "(1)"]
#check (IsRegularLocalRing.MvPowerSeries.exists_residueField_ringEquiv_of_ringChar_eq
  (R := R) : ringChar R = ringChar (ResidueField R) →
    ∃ (σ : Type) (_ : Finite σ),
      Nonempty (MvPowerSeries σ (ResidueField R) ≃+* R))

end

section

variable {R : Type u} [CommRing R] [IsCompleteLocalRing R] [IsRegularLocalRing R]
variable {k : Type v} [Field k] [Algebra k R]

/- Lemma 10.160.10 (2), tag `0C0S`: a coefficient field mapping bijectively to the residue field
gives a finite-variable formal power-series algebra presentation. -/
@[stacks 0C0S "(2)"]
#check (IsRegularLocalRing.MvPowerSeries.exists_algEquiv_of_residueField_bijective
  (R := R) (k := k) : Function.Bijective (ResidueField.map (algebraMap k R)) →
    ∃ (σ : Type) (_ : Finite σ), Nonempty (MvPowerSeries σ k ≃ₐ[k] R))

end
