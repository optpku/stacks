/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {k : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V]

/- Domain-style sampling for Lemma 9.4.1:
- primary domain: linear algebra over a field, specifically the freeness of vector spaces;
- sampled owner declarations:
  `Module.Free`,
  `Module.Free.of_basis`,
  `Module.Free.chooseBasis`,
  `Module.Free.of_divisionRing`;
- best owner abstraction: `Module.Free k V`;
- primitive data: none in this file beyond the ambient field/module structure, since freeness is
  already owned canonically by the `Module.Free` class;
- derived API: any chosen basis or coordinate description, for example via
  `Module.Free.chooseBasis`, is downstream derived data and should not be made primitive here.

Source/core/bridge triage:
- `source-facing`: the statement that every `k`-module is free when `k` is a field;
- `core/canonical`: the owner predicate `Module.Free k V`;
- `bridge/view`: the field-specialized check of the existing division-ring instance
  `Module.Free.of_divisionRing`.

This item is therefore a `bridge/view` check. The faithful refinement is to reuse the existing
owner-level theorem directly, rather than introduce any local wrapper or a basis-valued
reformulation as a new public API. -/

/- Lemma 9.4.1: if `k` is a field, then every `k`-module is a free `k`-module. This is the
canonical mathlib theorem `Module.Free.of_divisionRing`, specialized to the field case. -/
@[stacks 09FN]
#check Module.Free.of_divisionRing
