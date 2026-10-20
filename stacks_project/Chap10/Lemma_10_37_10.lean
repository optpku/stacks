module

public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
public import ReasLib.RingTheory.Normal.Ring
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.37.10
@stack 030B
-/

universe u

/-
Lemma 10.37.10 is a `source-facing` TFAE statement. Its `core/canonical` owner abstractions are
`IsIntegrallyClosed` for the global normal-domain clause and `IsNormalRing` for the all-prime
localization clause; the maximal-localization clause is the corresponding `bridge/view`.
-/
/- Lemma 10.37.10: for a domain `R`, the following are equivalent: `R` is a normal domain, every
localization `Rₚ` at a prime ideal is a normal domain, and every localization `Rₘ` at a maximal
ideal is a normal domain. Using `Definition 10.37.1` and `Definition 10.37.11`, these are
expressed by `IsIntegrallyClosed R`, `IsNormalRing R`, and the corresponding maximal
localizations. -/
@[stacks 030B "(1) implies (2), canonical normal-ring instance"]
#check @IsNormalRing.of_isIntegrallyClosed

@[stacks 030B "(2) implies (1), normal domains are integrally closed"]
#check @IsNormalRing.isIntegrallyClosed

@[stacks 030B "(2) implies (3), prime-localization owner"]
#check @IsNormalRing.isIntegrallyClosed_localizationAtPrime

@[stacks 030B "(3) implies (1), maximal-localization converse"]
#check @IsIntegrallyClosed.of_isLocalization_maximal
