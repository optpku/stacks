/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Etale.Basic
import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.LocalRing.Unibranch
public import ReasLib.RingTheory.RingHom.Local.AtPrime
public import ReasLib.RingTheory.Unramified.Basic

@[expose] public section

/-!
# Etale basic opens over geometrically unibranch points

This leaf owns the local algebra statement that an unramified map from a
domain becomes etale on a principal open when the source prime localization
is geometrically unibranch and the induced map of local rings is injective.
The target prime determines its contraction, so no separate prime or
`LiesOver` witness is part of the reusable interface.

@stack 0GSC
-/

universe u v

namespace Algebra.UnramifiedAt

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B] [Algebra A B] [IsDomain A]

/-- An unramified algebra map from a domain is etale on a basic open around `q`
when the source localization at the contracted prime is geometrically
unibranch and the canonical map of local rings is injective. -/
@[stacks 0GSC "Lemma 15.108.2"]
theorem exists_etale_away_of_geometricallyUnibranch_of_injective
    (q : PrimeSpectrum B)
    [IsGeometricallyUnibranch (Localization.AtPrime (q.asIdeal.under A))]
    (h_unramified : Algebra.UnramifiedAt A B q)
    (h_injective : Function.Injective ((algebraMap A B).localRingHomAt q)) :
    ∃ g : B, g ∉ q.asIdeal ∧ Algebra.Etale A (Localization.Away g) := sorry
-- Proof strategy: shrink to a standard-etale neighborhood, select the branch determined by
-- the injective local map, and descend the resulting iterated localization to one basic open.

end Algebra.UnramifiedAt
