module

public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Monoid.Prod
public import Mathlib.Data.Prod.Lex
public import Mathlib.RingTheory.HahnSeries.Summable
public import Mathlib.RingTheory.HahnSeries.Valuation
public import Mathlib.RingTheory.Valuation.ValuationRing
public import ReasLib.RingTheory.KrullDimension.Prime.FiniteSpectrum

/-!
# Rank-two lexicographic Hahn valuation integers

The valuation ring of `k⟦ℤ ×ₗ ℤ⟧` for the order valuation associated to the
lexicographic product value group has finite prime spectrum and Krull dimension
strictly greater than one.
-/

@[expose] public section

universe u

namespace HahnSeries

/-- The multiplicative valuation on Hahn series `k⟦ℤ ×ₗ ℤ⟧` associated to the
additive order valuation of the lexicographic product group. -/
noncomputable def lexProdValuation (k : Type u) [Field k] :
    Valuation k⟦ℤ ×ₗ ℤ⟧ (Multiplicative (WithTop (ℤ ×ₗ ℤ))ᵒᵈ) :=
  (addVal (ℤ ×ₗ ℤ) k).toValuation

/-- The valuation ring of `k⟦ℤ ×ₗ ℤ⟧` for the rank-two lexicographic Hahn valuation. -/
noncomputable abbrev lexProdInteger (k : Type u) [Field k] :=
  (lexProdValuation k).integer

/-- The rank-two lexicographic Hahn valuation integer ring over a field has
finitely many prime ideals. -/
instance instFinitePrimeSpectrum_lexProdInteger (k : Type u) [Field k] :
    Finite (PrimeSpectrum (lexProdInteger k)) := sorry

/-- The rank-two lexicographic Hahn valuation integer ring over a field has
Krull dimension strictly greater than one. -/
theorem one_lt_ringKrullDim_lexProdInteger (k : Type u) [Field k] :
    1 < ringKrullDim (lexProdInteger k) := sorry

/-- The rank-two lexicographic Hahn valuation integer ring over a field is
not Noetherian. -/
theorem not_isNoetherianRing_lexProdInteger (k : Type u) [Field k] :
    ¬ IsNoetherianRing (lexProdInteger k) := sorry

end HahnSeries
