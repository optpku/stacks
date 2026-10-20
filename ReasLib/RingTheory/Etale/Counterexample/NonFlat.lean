/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.HahnSeries.Summable
public import Mathlib.RingTheory.HahnSeries.Valuation
public import Mathlib.RingTheory.Valuation.ValuationRing
public import ReasLib.RingTheory.Ideal.Quotient.FormallyEtale
public import ReasLib.RingTheory.LocalRing.ResidueField.NonFlat

@[expose] public section

universe u

namespace HahnSeries

/-- The multiplicative valuation on Hahn series `k⟦ℚ⟧` associated to the
additive order valuation. -/
noncomputable def ratValuation (k : Type u) [Field k] :
    Valuation k⟦ℚ⟧ (Multiplicative (WithTop ℚ)ᵒᵈ) :=
  (addVal ℚ k).toValuation

/-- The valuation ring of `k⟦ℚ⟧` for the rational-order Hahn valuation. -/
noncomputable abbrev ratInteger (k : Type u) [Field k] :=
  (ratValuation k).integer

/-- The residue map of the rational-order Hahn valuation ring. -/
noncomputable def ratResidue (k : Type u) [Field k] :
    ratInteger k →+* IsLocalRing.ResidueField (ratInteger k) :=
  IsLocalRing.residue (ratInteger k)

/-- The maximal ideal of the rational-order Hahn valuation ring is idempotent. -/
theorem ratInteger_maximalIdeal_isIdempotentElem {k : Type u} [Field k] :
    IsIdempotentElem (IsLocalRing.maximalIdeal (ratInteger k)) := sorry

/-- The residue map of the rational-order Hahn valuation ring is formally étale. -/
theorem ratResidue_formallyEtale {k : Type u} [Field k] :
    (ratResidue k).FormallyEtale := sorry

/-- The residue map of the rational-order Hahn valuation ring is not flat. -/
theorem ratResidue_not_flat {k : Type u} [Field k] :
    ¬ (ratResidue k).Flat := sorry

end HahnSeries

namespace RingHom

/-- There exist formally étale ring maps that are not flat. -/
theorem exists_formallyEtale_not_flat :
    ∃ (R S : Type u) (_ : CommRing R) (_ : CommRing S) (f : R →+* S),
      f.FormallyEtale ∧ ¬ f.Flat := sorry

end RingHom
