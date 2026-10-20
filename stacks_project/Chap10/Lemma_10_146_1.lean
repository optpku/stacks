/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Unramified.LocalStructure
public import ReasLib.RingTheory.LocalRing.Quotient
public import ReasLib.RingTheory.RingHom.FormallyEtale.QuotientPow
import StacksCheckRecall

/-!
# Principal quotients of a local étale map

@stack 0GSD

The standard-étale chart, residue-field shift, and localization-section
calculations are proof infrastructure.  The public chapter bridge keeps the
source's positive-power quotient statement and points to the canonical formal
étale quotient-power owner.
-/

@[expose] public section

universe u v

open IsLocalRing

namespace Algebra

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]

#check @Algebra.Etale.formallyEtale
#check @Algebra.IsEtaleAt.exists_isStandardEtale
#check @RingHom.FormallyEtale.quotientMap_pow_bijective
#check @Ideal.span_singleton_pow

/-- Lemma 10.146.1 (0GSD): if a local map `R → S` is a localization of an
étale `R`-algebra and induces a bijection on residue fields, then some
`t ∈ maximalIdeal R` makes every positive-power quotient map bijective. -/
@[stacks 0GSD]
theorem exists_maximalIdealElement_forall_bijective_powQuotientMap
    (het : ∃ (T : Type (max u v)) (_ : CommRing T) (_ : Algebra R T) (_ : Algebra T S)
      (_ : IsScalarTower R T S) (_ : Etale R T) (M : Submonoid T),
        IsLocalization M S)
    (hres : Function.Bijective (ResidueField.map (algebraMap R S))) :
    ∃ t ∈ maximalIdeal R, ∀ n : ℕ+,
      Function.Bijective
        ((Ideal.quotientMap
            (Ideal.map (algebraMap R S) (Ideal.span ({t ^ (n : ℕ)} : Set R)))
            (algebraMap R S) Ideal.le_comap_map) :
          R ⧸ Ideal.span ({t ^ (n : ℕ)} : Set R) →+*
            S ⧸ Ideal.map (algebraMap R S) (Ideal.span ({t ^ (n : ℕ)} : Set R))) := sorry

end

end Algebra
