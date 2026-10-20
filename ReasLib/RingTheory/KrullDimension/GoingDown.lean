module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.RingTheory.Ideal.GoingDown
public import ReasLib.RingTheory.KrullDimension.Fiber

@[expose] public section

/-!
# Local dimension formulas for going-down maps

@stack 00ON

This leaf packages the local Krull-dimension equalities induced by a
Noetherian algebra map with going down.
-/

universe u v

namespace Algebra.GoingDown

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [IsNoetherianRing R] [IsNoetherianRing S] [Algebra.HasGoingDown R S]

/-- The Krull dimension of `S_q` is the sum of the dimensions of `R_(q ∩ R)` and of the local
fiber ring at `q`. -/
@[stacks 00ON]
theorem krullDim_eq_add_fiberDim (q : PrimeSpectrum S) :
    ringKrullDim (Localization.AtPrime q.asIdeal) =
      ringKrullDim (Localization.AtPrime (q.asIdeal.under R)) +
        ringKrullDim (fiberLocalRingAt R S q) := sorry

/-- For a finite going-down algebra, localization at a target prime has the same Krull dimension
as localization at its contracted prime. -/
@[stacks 00ON "finite going-down local dimension equality"]
theorem krullDim_localizationAtPrime_eq_under_of_finite
    [Module.Finite R S] (q : PrimeSpectrum S) :
    ringKrullDim (Localization.AtPrime q.asIdeal) =
      ringKrullDim (Localization.AtPrime (q.asIdeal.under R)) := sorry

/-- The height of a prime is the sum of the height of its contraction and the height of its
canonical fiber prime. -/
@[stacks 00ON "prime-height form"]
theorem height_eq_under_add_fiberPrimeHeight (q : PrimeSpectrum S) :
    q.asIdeal.height =
      (q.asIdeal.under R).height + (fiberPrimeAt R S q).asIdeal.height := sorry

/-- If `q` lies over `p`, then the height of `q` is the sum of the height of `p`
and the height of the canonical fiber prime at `q`. -/
@[stacks 00ON "prime-height form"]
theorem height_eq_comap_add_fiberPrimeHeight
    {p : PrimeSpectrum R} (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p) :
    q.asIdeal.height = p.asIdeal.height + (fiberPrimeAt R S q).asIdeal.height := sorry

/-- If `q` lies over `p`, then the Krull dimension of the localization at `q`
is the sum of the Krull dimension of the localization at `p` and that of the
local fiber ring at `q`. -/
theorem krullDim_eq_add_fiberDim_of_liesOver
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] (hq : q.LiesOver p) :
    ringKrullDim (Localization.AtPrime q) =
      ringKrullDim (Localization.AtPrime p) +
        ringKrullDim (fiberLocalRingAt R S ⟨q, inferInstance⟩) := sorry

/-- The Krull dimension of the localization at `q` is the sum of the dimension
of the localization at its contraction and the dimension of its quotient by
the extended contracted prime. -/
theorem krullDim_eq_add_quotientDim (q : PrimeSpectrum S) :
    ringKrullDim (Localization.AtPrime q.asIdeal) =
      ringKrullDim (Localization.AtPrime (q.asIdeal.under R)) +
        ringKrullDim
          ((Localization.AtPrime q.asIdeal) ⧸
            Ideal.map (algebraMap R (Localization.AtPrime q.asIdeal)) (q.asIdeal.under R)) := sorry

/-- If `q` lies over `p`, then the Krull dimension of the localization at `q`
is the sum of the dimension of the localization at `p` and the dimension of
the quotient by the extension of `p`. -/
theorem krullDim_eq_add_quotientDim_of_liesOver
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] (hq : q.LiesOver p) :
    ringKrullDim (Localization.AtPrime q) =
      ringKrullDim (Localization.AtPrime p) +
        ringKrullDim ((Localization.AtPrime q) ⧸
          Ideal.map (algebraMap R (Localization.AtPrime q)) p) := sorry

end Algebra.GoingDown
