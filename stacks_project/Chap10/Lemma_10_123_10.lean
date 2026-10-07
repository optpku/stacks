module

public import Mathlib.RingTheory.ZariskisMainTheorem
import StacksCheckRecall

@[expose] public section

/-!
Lemma 10.123.10 (Tag 00Q2): the reduced-ring version of the strong-transcendence obstruction.

@stack 00Q2
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Lemma 10.123.10:
- primary domain: strong transcendence and quasi-finiteness in commutative algebra;
- sampled owner declarations:
  `IsStronglyTranscendental`,
  `Algebra.QuasiFiniteAt`,
  `Algebra.not_isStronglyTranscendental_of_quasiFiniteAt`;
- best owner abstraction: the Mathlib theorem
  `Algebra.not_isStronglyTranscendental_of_quasiFiniteAt`;
- primitive data: `x : S`, its strong transcendence over `R`, finiteness of `Polynomial.aeval x`,
  and the prime `q`;
- derived API: the reduced-ring wording from the source, whose extra reducedness and
  `FaithfulSMul` assumptions are redundant for the canonical conclusion.

Source/core/bridge triage:
- `source-facing`: the Stacks negation of quasi-finiteness for a ring finite over `R[x]`;
- `core/canonical`: `IsStronglyTranscendental`, `Algebra.QuasiFiniteAt`, and the Mathlib owner
  theorem `Algebra.not_isStronglyTranscendental_of_quasiFiniteAt`;
- `bridge/view`: the owner is stronger than the source formulation: it needs only reducedness of
  the target, while reducedness of the base and faithful scalar action are redundant.  Taking its
  contrapositive gives the source's non-quasi-finiteness statement. -/

@[stacks 00Q2 "canonical strong-transcendence obstruction"]
#check @Algebra.not_isStronglyTranscendental_of_quasiFiniteAt
