/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Localization.FractionRing
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-
Domain-style sampling for Example 9.3.4:
- primary domain: fraction fields and their universal property for integral domains;
- sampled owner API:
  `FractionRing`,
  `FractionRing.field`,
  `IsFractionRing.injective`,
  `IsFractionRing.lift`;
- best owner abstraction: the quotient-field owner `FractionRing A` together with the canonical
  embedding `algebraMap A (FractionRing A)` and the interface `IsFractionRing A (FractionRing A)`.

Primitive-vs-derived split:
- primitive data: the owner type `FractionRing A` and its canonical embedding
  `algebraMap A (FractionRing A)`;
- derived API: the field structure on `FractionRing A`, the instance
  `IsFractionRing A (FractionRing A)`, injectivity of the canonical embedding, and the universal
  property morphism `IsFractionRing.lift`.

Source/core/bridge triage:
- `source-facing`: the quotient field of `A` and its canonical embedding into a field;
- `core/canonical`: `FractionRing A`;
- `bridge/view`: `IsFractionRing.lift`, expressing the universal property of the quotient field.

This file should therefore check `FractionRing` and its canonical embedding/interface directly,
and keep `IsFractionRing.lift` only as the universal-property companion.
-/

section

variable {A : Type u} [CommRing A] [IsDomain A] {K : Type v} [Field K]

/-
Example 9.3.4 (Quotient fields): the quotient field of a domain `A` is the canonical owner
construction `FractionRing A`.
-/
@[stacks 09FJ]
#check (FractionRing A : Type u)

/- Companion check: when `A` is a domain, `FractionRing A` carries its canonical field
structure. -/
#check FractionRing.field

/- Companion check: the quotient field of a domain is canonically a fraction ring of that
domain. -/
#check (inferInstance : IsFractionRing A (FractionRing A))

/- Companion check: the canonical embedding of `A` into its quotient field is `algebraMap`. -/
#check (algebraMap A (FractionRing A) : A →+* FractionRing A)

/- Companion check: the canonical embedding `A → FractionRing A` is injective. -/
#check (IsFractionRing.injective A (FractionRing A) :
    Function.Injective (algebraMap A (FractionRing A)))

/- Companion checks: every injective ring map from `A` to a field extends uniquely from the
quotient field. -/
#check IsFractionRing.lift
#check IsFractionRing.lift_unique
#check IsFractionRing.lift_algebraMap

end
