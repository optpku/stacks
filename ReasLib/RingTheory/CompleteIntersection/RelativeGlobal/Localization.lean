/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CompleteIntersection.RelativeGlobal.Basic
public import ReasLib.RingTheory.KrullDimension.Presentation
public import ReasLib.RingTheory.KrullDimension.Relative.FiniteType
public import ReasLib.RingTheory.KrullDimension.Relative.Transport

@[expose] public section

/-!
# Principal Charts of Relative Global Complete Intersections

@stack 00ST

This leaf turns dimension information for a fixed finite presentation into
relative-global-complete-intersection principal charts.  It deliberately
returns the canonical localization `Localization.Away g`; explicit
inverse-adjoining quotient models belong to source-facing companions.
-/

universe u v

namespace Algebra.Presentation.RelativeGlobal

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {n c : ℕ}

/-- A finite presentation produces a relative global complete-intersection
principal chart whenever the chart lies in its bounded relative-dimension
locus. -/
@[stacks 00ST "relative global complete intersection principal chart"]
theorem localizationAway_of_basicOpen_subset_relativeDimensionAtLELocus
    (P : Presentation R S (Fin n) (Fin c)) (hcard : c ≤ n) (g : S)
    (hbasic : (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) ⊆
      relativeDimensionAtLELocus R S P.dimension) :
    Algebra.IsRelativeGlobalCompleteIntersection R (Localization.Away g) := sorry

/-- Lemma 10.136.10 (1), tag `00ST`, at the presentation level: expected
fiber dimensions over a closed base subscheme produce a relative global
complete-intersection principal chart that is the identity modulo that
subscheme. -/
@[stacks 00ST "relative global complete intersection chart over a closed base subscheme"]
theorem exists_localizationAway_of_fiberDimension_on_closedSet
    (P : Presentation R S (Fin n) (Fin c)) (hcard : c ≤ n) (I : Ideal R)
    (hdim : ∀ p : PrimeSpectrum R, I ≤ p.asIdeal →
      Nonempty (PrimeSpectrum (p.asIdeal.Fiber S)) →
        ringKrullDim (p.asIdeal.Fiber S) = P.dimension) :
    ∃ g : S, Ideal.Quotient.mk (Ideal.map (algebraMap R S) I) g = 1 ∧
      Algebra.IsRelativeGlobalCompleteIntersection R (Localization.Away g) := sorry

/-- Lemma 10.136.10 (2), tag `00ST`, at the presentation level: an expected
dimension fiber has a relative global complete-intersection principal chart
whose generator is a unit on that fiber. -/
@[stacks 00ST "relative global complete intersection chart at a base prime"]
theorem exists_localizationAway_of_fiberDimension_atPrime
    (P : Presentation R S (Fin n) (Fin c)) (hcard : c ≤ n) (p : PrimeSpectrum R)
    (hdim : ringKrullDim (p.asIdeal.Fiber S) = P.dimension) :
    ∃ g : S,
      IsUnit ((Algebra.TensorProduct.includeRight : S →ₐ[R] p.asIdeal.Fiber S) g) ∧
        Algebra.IsRelativeGlobalCompleteIntersection R (Localization.Away g) := sorry

/-- Lemma 10.136.10 (3), tag `00ST`, at the presentation level: expected
relative dimension at a target prime produces a relative global
complete-intersection principal neighborhood of that prime. -/
@[stacks 00ST "relative global complete intersection chart at a target prime"]
theorem exists_localizationAway_of_relativeDimensionAt
    (P : Presentation R S (Fin n) (Fin c)) (hcard : c ≤ n) (q : PrimeSpectrum S)
    (hdim : relativeDimensionAt R S q = P.dimension) :
    ∃ g : S, g ∉ q.asIdeal ∧
      Algebra.IsRelativeGlobalCompleteIntersection R (Localization.Away g) := sorry

end Algebra.Presentation.RelativeGlobal
