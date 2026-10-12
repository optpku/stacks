/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Smooth.AtPrime
public import ReasLib.Data.Set.PowersetCard.Fin
public import ReasLib.RingTheory.Smooth.Standard.Element.Selected

/-!
# Standard neighborhoods of smooth points

This leaf expresses smoothness at a prime by elementary and strict standard
principal neighborhoods.
-/

@[expose] public section

universe u v

namespace Algebra

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

namespace SmoothAtPrime

/-- Lemma 16.2.2: in a fixed finite presentation, every smooth prime has an
elementary standard principal neighborhood obtained from selected equally sized
sets of variables and relations. -/
@[stacks 07C6]
theorem exists_isElementaryFor
    {n m : ℕ} (P : Presentation R A (Fin n) (Fin m))
    (q : PrimeSpectrum A) (hq : SmoothAtPrime R A q) :
    ∃ (a : A) (c : ℕ) (U : Set.powersetCard (Fin n) c)
      (V : Set.powersetCard (Fin m) c),
      a ∉ q.asIdeal ∧
        P.IsElementaryFor a (U.1.orderEmbOfFin U.2).toEmbedding
          (V.1.orderEmbOfFin V.2).toEmbedding := sorry

variable [FinitePresentation R A]

/-- A smooth point of a finitely presented algebra has an elementary standard
principal neighborhood. -/
@[stacks 07C6 "presentation-independent elementary standard neighborhood"]
theorem exists_not_mem_elementaryStandard
    (q : PrimeSpectrum A) (hq : SmoothAtPrime R A q) :
    ∃ a : A, a ∉ q.asIdeal ∧ IsElementaryStandard R a := sorry

/-- A smooth point of a finitely presented algebra has a strictly standard
principal neighborhood. -/
@[stacks 07C6 "strictly standard neighborhood of a smooth point"]
theorem exists_not_mem_strictlyStandard
    (q : PrimeSpectrum A) (hq : SmoothAtPrime R A q) :
    ∃ a : A, a ∉ q.asIdeal ∧ IsStrictlyStandard R a := sorry

end SmoothAtPrime

end Algebra
