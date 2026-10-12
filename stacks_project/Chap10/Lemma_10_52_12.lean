/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.Length.Semilocal
import StacksCheckRecall

/-!
# Length under a local base ring

Lemma 10.52.12 expresses the length over a local base as the residue-degree-weighted sum of
the localized lengths over a semilocal algebra, and deduces finite length after restriction of
scalars. The `finsum` theorem is the canonical enumeration-free owner; the finite-sum theorem is
its source-facing specialization.

@stack 02M0
-/

@[expose] public section

@[stacks 02M0 "enumeration-free length formula"]
#check @Module.length_eq_finsum_inertiaDeg_mul_localized

@[stacks 02M0 "finite maximal-spectrum length formula"]
#check @Module.length_eq_sum_inertiaDeg_mul_localized

@[stacks 02M0 "finite-length consequence"]
#check @Module.isFiniteLength_restrictScalars_of_residueFinite
