/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.Separable.Generated.Properties
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/-!
Domain-style sampling for Lemma 10.42.2:
- primary domain: Stacks Project separability for field extensions and intermediate fields;
- sampled owner declarations:
  `Algebra.IsSeparableOver`,
  `Algebra.IsSeparableOver.of_intermediateField`,
  `Algebra.IsSeparableOver.of_algEquiv`,
  `Algebra.IsSeparableOver.isSeparable`;
- best owner abstraction: the chapter owner predicate `Algebra.IsSeparableOver`;
- primitive data: the owner predicate on `K / k` together with an intermediate field `K'`;
- derived API: transport to intermediate fields, transport across algebra equivalences, and the
  algebraic specialization to `Algebra.IsSeparable`.

Layer triage:
- `source-facing`: stability of Stacks Project separability under passing to an intermediate field;
- `core/canonical`: `Algebra.IsSeparableOver`;
- `bridge/view`: the owner theorem `Algebra.IsSeparableOver.of_intermediateField`.

Since Definition 10.42.1 already introduced the owner predicate and this lemma adds no new data,
the file should remain a pure recall surface rather than a parallel local theorem or wrapper.

@stack 030P
-/

/- Lemma 10.42.2: if `K / k` is separable in the Stacks Project sense and `K'` is an
intermediate field in the tower `K / K' / k`, then the subextension `K' / k` is separable in the
same sense. -/
@[stacks 030P]
#check @Algebra.IsSeparableOver.of_intermediateField
#check @Algebra.IsSeparableOver.of_intermediateField_of
#check @Algebra.IsSeparableOver.of_algEquiv
#check @Algebra.IsSeparableOver.of_algEquiv_of
