/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Etale.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.150.5

@stack 04EG
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling:
- primary domain: formal étaleness of commutative algebras, specialized to localization;
- sampled owner API:
  `Algebra.FormallyEtale`,
  `Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth`,
  `Algebra.FormallyEtale.of_isLocalization`,
  `Algebra.FormallySmooth.of_isLocalization`;
- source-facing: the textbook lemma that the localization map `R → M⁻¹R` is formally étale;
- core/canonical: the mathlib owner class `Algebra.FormallyEtale`;
- bridge/view: none; the source statement is exactly the owner-level localization theorem.

Primitive data are the commutative ring, the multiplicative subset, and the localization instance.
Formal étaleness is derived API owned upstream by `Algebra.FormallyEtale.of_isLocalization`, so
this file should recall that owner theorem directly rather than keep any parallel local wrapper.
-/

/- Lemma 10.150.5: for a commutative ring `R` and a multiplicative subset `M`, the localization
map `R → M⁻¹R` is formally étale. This is exactly the canonical localization theorem
`Algebra.FormallyEtale.of_isLocalization`. -/
@[stacks 04EG]
#check @Algebra.FormallyEtale.of_isLocalization
