module

public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Etale algebras over Dedekind domains

This leaf records the finite-product theorem for an etale algebra over a Dedekind domain.  Since
Mathlib's `IsDedekindDomain` includes fields while `IsDiscreteValuationRing` excludes them, the
local consequence is exposed as the precise field-or-DVR alternative, together with its two
contraction branches.

@stack 0AP2
-/

@[expose] public section

universe u v

namespace Algebra.Etale

/-- Lemma 15.44.4 (Stacks `0AP2`): an etale algebra over a Dedekind domain is a finite product
of Dedekind domains. -/
@[stacks 0AP2 "finite product of Dedekind domains"]
theorem exists_finiteProductOfDedekindDomains
    {A : Type u} {B : Type v} [CommRing A] [IsDedekindDomain A]
    [CommRing B] [Algebra A B] [Algebra.Etale A B] :
    ∃ (ι : Type (max u v)) (_ : Finite ι) (R : ι → Type (max u v))
      (_ : ∀ i, CommRing (R i)) (_ : ∀ i, IsDedekindDomain (R i)),
      Nonempty (B ≃+* ∀ i, R i) := sorry

/-- A maximal localization whose prime contracts to zero is a field. -/
@[stacks 0AP2 "zero-contraction local branch"]
theorem localizationAtMaximal_isField_of_under_eq_bot
    {A : Type u} {B : Type v} [CommRing A] [IsDedekindDomain A]
    [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (q : MaximalSpectrum B) (hq : q.asIdeal.under A = ⊥) :
    IsField (Localization.AtPrime q.asIdeal) := sorry

/-- A maximal localization whose prime has nonzero contraction is a discrete valuation ring. -/
@[stacks 0AP2 "nonzero-contraction local branch"]
theorem localizationAtMaximal_isDVR_of_under_ne_bot
    {A : Type u} {B : Type v} [CommRing A] [IsDedekindDomain A]
    [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (q : MaximalSpectrum B) (hq : q.asIdeal.under A ≠ ⊥) :
    ∃ (_ : IsDomain (Localization.AtPrime q.asIdeal)),
      IsDiscreteValuationRing (Localization.AtPrime q.asIdeal) := sorry

/-- Every maximal localization of an etale algebra over a Dedekind domain is either a field or a
discrete valuation ring.  The field alternative is necessary because Mathlib regards fields as
Dedekind domains. -/
@[stacks 0AP2 "local field-or-DVR consequence"]
theorem localizationAtMaximal_isField_orDVR
    {A : Type u} {B : Type v} [CommRing A] [IsDedekindDomain A]
    [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (q : MaximalSpectrum B) :
    IsField (Localization.AtPrime q.asIdeal) ∨
      ∃ (_ : IsDomain (Localization.AtPrime q.asIdeal)),
        IsDiscreteValuationRing (Localization.AtPrime q.asIdeal) := sorry

end Algebra.Etale
