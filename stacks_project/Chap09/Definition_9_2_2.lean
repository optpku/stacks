/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Ring.Basic
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 9.2.2: in the chapter's commutative-ring setting, the Stacks notion of an integral
domain is expressed by the canonical mathlib owner `IsDomain`; on a ring this is equivalent to
being nontrivial and having no zero divisors. -/
@[stacks 09FE]
#check IsDomain

/- Definition 9.2.2 companion: on a ring, the source wording "nonzero and with `0` as the only
zerodivisor" is exactly the canonical theorem `isDomain_iff_noZeroDivisors_and_nontrivial`. -/
#check isDomain_iff_noZeroDivisors_and_nontrivial
