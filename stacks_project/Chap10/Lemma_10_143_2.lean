/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Algebra

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-! @stack 00U9 -/

/-
Domain-style sampling for Lemma 10.143.2:
- primary domain: commutative-algebraic smoothness and étaleness for `R`-algebras;
- sampled owner declarations:
  `Algebra.Etale`,
  `Algebra.IsStandardSmoothOfRelativeDimension`,
  `Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero`,
  `RingHom.etale_iff_isStandardSmoothOfRelativeDimension_zero`;
- best owner abstraction: the algebra-level equivalence
  `Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero`;
- primitive data: the owner predicates `Etale R S` and `IsStandardSmoothOfRelativeDimension 0 R S`;
- derived API: the forward and backward implications, plus the ring-hom bridge theorem.

Layer triage:
- `source-facing`: the Stacks lemma asserting that étale implies standard smooth of relative
  dimension `0`;
- `core/canonical`: the upstream equivalence
  `Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero`;
- `bridge/view`: the ring-hom reformulation
  `RingHom.etale_iff_isStandardSmoothOfRelativeDimension_zero`.

The source entry is the forward implication; the stronger owner equivalence is retained as an
untagged companion rather than silently replacing the source statement.
-/

/- Lemma 10.143.2 (00U9): the source-facing assertion is the forward direction from an etale
algebra to a standard-smooth presentation of relative dimension `0`.  The canonical owner also
records the converse, which is useful independently of this textbook item. -/
@[stacks 00U9 "etale maps are standard smooth"]
#check ((Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero (R := R) (S := S)).mp :
  Algebra.Etale R S → IsStandardSmoothOfRelativeDimension 0 R S)

/- The converse is part of the reusable owner API, but is not asserted by this source item. -/
#check @Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero

end Algebra
