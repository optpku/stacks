/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.RingTheory.Normal.Ring
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite products of normal domains

This leaf owns the finite-minimal-prime decomposition criterion for a reduced normal ring.  The
finite product is kept as a proposition-valued TFAE clause, while the concrete product equivalence
is supplied by the existential exactly as in the source theorem.

@stack 030C
-/

@[expose] public section

universe u v

namespace Localization.AtPrime

/-- Evaluation at one factor of a product identifies the corresponding prime localizations, so
fieldness is preserved. -/
@[stacks 030C "fieldness under localization at a product factor"]
theorem isField_piEval_iff
    {ι : Type u} {R : ι → Type v} [∀ i, CommRing (R i)] (i : ι)
    (P : PrimeSpectrum (R i)) :
    IsField (Localization.AtPrime (Ideal.comap (Pi.evalRingHom R i) P.asIdeal)) ↔
      IsField (Localization.AtPrime P.asIdeal) := sorry

end Localization.AtPrime

namespace IsNormalRing

/-- For a reduced ring with finitely many minimal primes, normality, integral closedness, and a
finite product of normal domains are equivalent conditions. -/
@[stacks 030C "finite-product normality criterion"]
theorem tfae_integrallyClosed_finiteProduct
    (R : Type u) [CommRing R] [IsReduced R] [Finite (minimalPrimes R)] :
    List.TFAE
      [ IsNormalRing R
      , IsIntegrallyClosed R
      , ∃ (ι : Type u) (_ : Finite ι) (S : ι → Type u) (_ : ∀ i, CommRing (S i))
          (_ : R ≃+* ∀ i, S i),
          (∀ i, IsDomain (S i)) ∧ ∀ i, IsIntegrallyClosed (S i)
      ] := sorry

end IsNormalRing
