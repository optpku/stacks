/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.KrullDimension.FiniteType.Local
import StacksCheckRecall

@[expose] public section

/-!
# Local Dimension of a Finite-Type Algebra

@stack 00P1
-/

universe u v

open TopologicalSpace

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

/- Lemma 10.116.3: at a point of the spectrum of a finite-type algebra over a
field, the local dimension is the dimension of the local ring plus the
transcendence degree of the residue field. -/
@[stacks 00P1]
#check
  (PrimeSpectrum.topologicalKrullDimAt_eq_ringKrullDim_localizationAtPrime_add_trdeg_residueField
    (k := k) (S := S) :
  ∀ x : PrimeSpectrum S,
    topologicalKrullDimAt x =
      ringKrullDim (Localization.AtPrime x.asIdeal) +
        Cardinal.toNat (Algebra.trdeg k x.asIdeal.ResidueField))
