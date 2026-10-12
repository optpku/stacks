/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReasLib.RingTheory.Valuation.Noetherian
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Discrete valuation ring characterizations

The primary interfaces in this leaf use the canonical typeclass assumptions for a Noetherian
local domain.  The existentially packaged TFAE from the chapter is retained below as a
source-facing bridge, so downstream developments can choose either the short canonical iff
statements or the literal list of alternatives.

@stack 09DZ
@stack 00PD
-/

@[expose] public section

universe u

open Ideal IsLocalRing

namespace IsDiscreteValuationRing

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

/-- Definition 10.119.8 (Stacks `09DZ`): a uniformizer is an element generating the maximal
ideal; the canonical DVR owner expresses this by irreducibility. -/
@[stacks 09DZ]
theorem maximalIdeal_eq_span_singleton_iff_irreducible (π : A) :
    maximalIdeal A = Ideal.span {π} ↔ Irreducible π := sorry

end IsDiscreteValuationRing

namespace IsDiscreteValuationRing

variable {A : Type u} [CommRing A] [IsDomain A]

/-- The canonical DVR criterion: a Noetherian local domain is a DVR exactly when it is regular
local of Krull dimension one. -/
@[stacks 00PD "regular-local characterization"]
theorem iff_regularLocalRing_dim_one :
    IsDiscreteValuationRing A ↔ IsRegularLocalRing A ∧ ringKrullDim A = 1 := sorry

end IsDiscreteValuationRing

namespace IsDiscreteValuationRing

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]

/-- A nonzero principal maximal ideal is equivalent to the DVR condition.  The nonzero clause is
kept in the proposition so callers do not have to manufacture a separate `¬ IsField A` witness. -/
@[stacks 00PD "principal maximal ideal characterization"]
theorem iff_maximalIdeal_isPrincipal :
    IsDiscreteValuationRing A ↔
      maximalIdeal A ≠ ⊥ ∧ (maximalIdeal A).IsPrincipal := sorry

/-- A Noetherian local domain is a DVR exactly when it is normal and one-dimensional. -/
@[stacks 00PD "normal dimension-one characterization"]
theorem iff_integrallyClosed_dim_one :
    IsDiscreteValuationRing A ↔ IsIntegrallyClosed A ∧ ringKrullDim A = 1 := sorry

/-- Construct a DVR from the normal one-dimensional local-domain criterion. -/
@[stacks 00PD "normal dimension-one construction"]
theorem of_integrallyClosed_dim_one [IsIntegrallyClosed A]
    (hdim : ringKrullDim A = 1) : IsDiscreteValuationRing A := sorry

/-- Construct a DVR from a nonzero principal maximal ideal in a Noetherian local domain. -/
@[stacks 00PD "principal maximal ideal construction"]
theorem of_maximalIdeal_isPrincipal
    (h : maximalIdeal A ≠ ⊥ ∧ (maximalIdeal A).IsPrincipal) :
    IsDiscreteValuationRing A := sorry

end IsDiscreteValuationRing

namespace IsDiscreteValuationRing

variable {A : Type u} [CommRing A] [IsDomain A]

/-- A regular local ring of Krull dimension one is a DVR.  The regular-local structure is accepted
as a proposition argument so callers holding a term need not install a temporary local instance. -/
@[stacks 00PD "regular-local construction"]
theorem of_regularLocalRing_dim_one
    (hreg : IsRegularLocalRing A) (hdim : ringKrullDim A = 1) :
    IsDiscreteValuationRing A := sorry

end IsDiscreteValuationRing

variable {A : Type u} [CommRing A]

/-- Lemma 10.119.7 (Stacks `00PD`): the source-facing five-way characterization of a discrete
valuation ring.  The canonical reusable views are the iff theorems in
`IsDiscreteValuationRing`. -/
@[stacks 00PD]
theorem discreteValuationRing_tfae :
    List.TFAE
      [ (∃ (_ : IsDomain A), IsDiscreteValuationRing A),
        ∃ (_ : IsDomain A) (_ : IsNoetherianRing A), ValuationRing A ∧ ¬ IsField A,
        IsRegularLocalRing A ∧ ringKrullDim A = 1,
        ∃ (_ : IsLocalRing A) (_ : IsNoetherianRing A) (_ : IsDomain A),
          maximalIdeal A ≠ ⊥ ∧ (maximalIdeal A).IsPrincipal,
        ∃ (_ : IsLocalRing A) (_ : IsNoetherianRing A) (_ : IsDomain A)
          (_ : IsIntegrallyClosed A), ringKrullDim A = 1 ] := sorry

/-- Source bridge for the regular-local clause of Lemma 10.119.7, retaining the chapter's
existential domain packaging. -/
@[stacks 00PD "source regular-local bridge"]
theorem discreteValuationRing_iff_regularLocalRing_dim_one :
    (∃ (_ : IsDomain A), IsDiscreteValuationRing A) ↔
      IsRegularLocalRing A ∧ ringKrullDim A = 1 := sorry

variable [IsDomain A] [IsDiscreteValuationRing A]

namespace IsDiscreteValuationRing

/-- Every nonzero element of a DVR has a unique unit-times-power normal form for a chosen
generator of the maximal ideal. -/
@[stacks 00PD "uniformizer normal form"]
theorem existsUnique_unit_mul_pow (π a : A)
    (hπ : maximalIdeal A = Ideal.span {π}) (ha : a ≠ 0) :
    ∃! p : Aˣ × ℕ, a = (p.1 : A) * π ^ p.2 := sorry

end IsDiscreteValuationRing
