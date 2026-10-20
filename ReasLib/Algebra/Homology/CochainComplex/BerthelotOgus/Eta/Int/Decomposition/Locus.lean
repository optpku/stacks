/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Int.Decomposition
public import ReasLib.Algebra.Homology.HomologicalComplex.Bockstein.Localization
public import ReasLib.RingTheory.Ideal.Localization
public import ReasLib.RingTheory.Ideal.Quotient.Prime

/-!
# Local behavior of eta decomposition ideals

At a prime where all reduced cycles lift, every degreewise product-splitting condition holds.
Consequently the total eta decomposition ideal vanishes after localization at the corresponding
prime of `A / (f)`.
@stack 0F81
-/

@[expose] public section

open CategoryTheory
open scoped nonZeroDivisors

noncomputable section

universe u v

namespace CochainComplex.BerthelotOgus.Int.Reduction.Decomposition

variable {A : Type u} [CommRing A]

/-- The prime of `A / (f)` induced by a prime of `A` containing `f`; this is the
Berthelot-Ogus specialization of `PrimeSpectrum.quotientOfLE`. -/
abbrev quotientPrime (f : A) (p : PrimeSpectrum A) (hpf : f ∈ p.asIdeal) :
    PrimeSpectrum (A ⧸ principalIdeal f) :=
  PrimeSpectrum.quotientOfLE (principalIdeal f) p
    (principalIdeal_le_iff_mem.mpr hpf)

/-- The total eta decomposition ideal localized at the quotient prime induced by `p`. -/
noncomputable def localizedIdeal
    (f : nonZeroDivisors A) (K : CochainComplex (ModuleCat.{max u v} A) ℤ)
    [K.IsTermwiseFiniteFree]
    (q : PrimeSpectrum (A ⧸ principalIdeal (f : A))) :
    Ideal (Localization.AtPrime q.asIdeal) :=
  (ideal f K).localizationAtPrime q

/-- At a prime in the cycles-lift locus, the localized total eta decomposition ideal is zero.
This strengthened form does not require boundedness. -/
theorem localizedIdeal_eq_bot_of_cyclesLift
    (f : nonZeroDivisors A) (K : CochainComplex (ModuleCat.{max u v} A) ℤ)
    [K.IsTermwiseFiniteFree]
    (hI : ∀ i : ℤ, (Int.etaDeterminantalIdeal (f : A) K i).IsPrincipal)
    (p : PrimeSpectrum A)
    (hp : p ∈ HomologicalComplex.Bockstein.cyclesLiftLocus (f : A) K) :
    localizedIdeal f K (quotientPrime (f : A) p hp.1) = ⊥ := sorry

/-- Lemma 15.97.9 (3), Tag 0F81: for a bounded complex and a prime in the cycles-lift locus,
the localized total eta decomposition ideal is zero. -/
@[stacks 0F81 "local vanishing of the total eta decomposition ideal"]
theorem localizedIdeal_eq_bot_of_mem_cyclesLiftLocus
    (f : nonZeroDivisors A) (K : CochainComplex (ModuleCat.{max u v} A) ℤ)
    [K.IsTermwiseFiniteFree]
    (hI : ∀ i : ℤ, (Int.etaDeterminantalIdeal (f : A) K i).IsPrincipal)
    (hbounded : CochainComplex.bounded (ModuleCat.{max u v} A) K)
    (p : PrimeSpectrum A)
    (hp : p ∈ HomologicalComplex.Bockstein.cyclesLiftLocus (f : A) K) :
    localizedIdeal f K (quotientPrime (f : A) p hp.1) = ⊥ := sorry

/-- If all localized cohomology modules are free, the prime lies in the Bockstein cycles-lift
locus.  This is the bounded finite-free source specialization. -/
@[stacks 0F81 "localized free cohomology lies in the Bockstein vanishing locus"]
theorem mem_cyclesLiftLocus_of_localizedHomology_free
    (f : nonZeroDivisors A) (K : CochainComplex (ModuleCat.{max u v} A) ℤ)
    (hbounded : CochainComplex.bounded (ModuleCat.{max u v} A) K)
    [K.IsTermwiseFiniteFree]
    (p : PrimeSpectrum A) (hpf : (f : A) ∈ p.asIdeal)
    (hH : ∀ i : ℤ,
      Module.Free (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal (K.homology i))) :
    p ∈ HomologicalComplex.Bockstein.cyclesLiftLocus (f : A) K := sorry

end CochainComplex.BerthelotOgus.Int.Reduction.Decomposition
