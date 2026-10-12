/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Jacobson.BasicOpen
import StacksCheckRecall

/-!
# Lemma 10.35.5

@stack 034J

The reusable owner separates the locally closed chart, its localized field, and the Jacobson
infinitude conclusion. This file records the source statement without its topology proof
scaffolding.
-/

/- Lemma 10.35.5 (1)-(3): a non-Jacobson ring has a nonmaximal prime isolated by a basic open in
its closure. The equality also implies that the chart function is not in the prime. -/
@[stacks 034J "non-Jacobson singleton chart"]
#check @PrimeSpectrum.exists_nonmaximal_basicOpen_inter_zeroLocus_eq_singleton_of_not_isJacobsonRing

/- Lemma 10.35.5 (4): the corresponding localization of the prime quotient is a field. -/
@[stacks 034J "singleton chart is a field"]
#check @PrimeSpectrum.isField_localizationAway_quotient_of_zeroLocus_inter_basicOpen_eq_singleton

/- Conversely, in a Jacobson ring the same chart for a nonmaximal prime is infinite. -/
@[stacks 034J "Jacobson charts are infinite"]
#check @PrimeSpectrum.infinite_zeroLocus_inter_basicOpen_of_isJacobsonRing
