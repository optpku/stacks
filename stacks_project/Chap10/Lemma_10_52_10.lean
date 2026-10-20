module

public import Mathlib.RingTheory.Length
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/-!
# Simple modules and length

@stack 00J2

Domain triage:
- `source-facing`: the lemma packages the textbook equivalence between simplicity, length `1`,
  and being a quotient by a maximal ideal.
- `core/canonical`: the owner abstraction is mathlib's `IsSimpleModule R M`.
- `bridge/view`: this file's theorem is the TFAE packaging of the two canonical characterizations
  `Module.length_eq_one_iff` and `isSimpleModule_iff_quot_maximal`.
- Primitive data vs derived API: there is no extra primitive data here beyond the owner notion;
  the length-one and quotient-by-a-maximal-ideal clauses are derived API.
-/
@[stacks 00J2 "(1) iff (2), length one"]
#check @Module.length_eq_one_iff

@[stacks 00J2 "(1) iff (3), maximal-ideal quotient"]
#check @isSimpleModule_iff_quot_maximal
