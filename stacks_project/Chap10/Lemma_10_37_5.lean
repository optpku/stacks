/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.Defs
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.37.5: any localization of a normal domain is normal.

The source-facing normality and domain conclusions are both recalled from the localization API.

@stack 00GY
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.37.5: any localization of a normal domain is again normal. Since
`Definition 10.37.1` identifies normal domains with integrally closed domains, the owner
abstraction here is `IsIntegrallyClosed`; `IsLocalization M S` with `hM : M ≤ R⁰` is the
primitive localization data, and the normality/domain conclusions are derived canonically. -/
@[stacks 00GY "normality under localization"]
#check @isIntegrallyClosed_of_isLocalization

/- Companion recall: under the same non-zero-divisor hypothesis, the localization is also a
domain via the canonical theorem `IsLocalization.isDomain_of_le_nonZeroDivisors`. -/
@[stacks 00GY "domain under localization"]
#check @IsLocalization.isDomain_of_le_nonZeroDivisors
