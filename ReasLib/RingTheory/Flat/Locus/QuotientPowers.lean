/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Flat.Locus.Closed
public import ReasLib.RingTheory.Flatness.QuotientPowers.LocalCriterion
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flatness loci from ideal-power quotients

This leaf globalizes the local ideal-power criterion over a closed subset of the source.
The hypothesis uses the canonical quotient of each localized module, which is the standard
owner-level presentation of the localized quotients in the source statement.

@stack 05LU
-/

@[expose] public section

open PrimeSpectrum

universe u v w

namespace Module.Flat.QuotientPowers

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

/-- Lemma 15.19.5: ideal-power quotient flatness at every prime in
`V(I.map (algebraMap R S) + J)` places that closed subset inside the flat-over-`R` locus. -/
@[stacks 05LU "Lemma 15.19.5"]
theorem zeroLocus_add_subset_flatOverBaseLocus
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Finite S M]
    (I : Ideal R) (J : Ideal S)
    (hquot : ∀ (q : PrimeSpectrum S)
      (_ : q ∈ zeroLocus ((I.map (algebraMap R S) + J : Ideal S) : Set S)),
      Module.Flat.QuotientPowers (R := R)
        (M := LocalizedModule.AtPrime q.asIdeal M) I) :
    zeroLocus ((I.map (algebraMap R S) + J : Ideal S) : Set S) ⊆
      Module.flatOverBaseLocus R S M := sorry
-- Proof strategy: rewrite the closed-subset inclusion with the canonical flat-locus membership
-- bridge.  For `q` in the zero locus, its defining ideal containment gives
-- `I.map (algebraMap R S) ≤ q.asIdeal`; map this inclusion to
-- `Localization.AtPrime q.asIdeal`, identify the target with its maximal ideal, and apply
-- `Module.Flat.QuotientPowers.atPrime` to `hquot q hq`.

end Module.Flat.QuotientPowers
