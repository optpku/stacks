/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import Mathlib.RingTheory.Jacobson.Ring

/-!
Definition 15.10.1 (0ELY): a Zariski pair `(A, I)` is a commutative ring together with an
ideal `I` contained in `Ring.jacobson A`. The canonical owner is the ideal-level containment
proposition, so this chapter file remains a source facade.
@stack 0ELY
-/

@[expose] public section

universe u

section

variable (A : Type u) [CommRing A]
variable (I : Ideal A)

/- Domain-style sampling for Zariski pairs and Jacobson-radical containment:
- primary domain: commutative-ring ideals and the Jacobson radical;
- sampled declarations: `Ideal.jacobson`, `Ideal.le_jacobson`, `Ideal.jacobson_bot`,
  `Ring.jacobson`;
- best owner abstraction: the canonical ideal-level owner `Ideal.jacobson`, exposed on a ring by
  the shorter surface `Ring.jacobson A`.

Layer triage:
- `source-facing`: the textbook condition that the ideal `I` lies in the Jacobson radical of `A`;
- `core/canonical`: the ideal-level owner `Ideal.jacobson`;
- `bridge/view`: `Ideal.jacobson_bot`, which identifies `⊥.jacobson` with `Ring.jacobson A`.

Primitive data is only the ideal `I`. The containment proposition `I ≤ Ring.jacobson A` is the
whole source-facing notion, and consequences such as the special case `I = ⊥` are derived API via
`Ideal.le_jacobson`. Therefore this file should expose the canonical containment proposition
directly rather than introduce a parallel `ZariskiPair` wrapper.
-/

/- Definition 15.10.1: a Zariski pair `(A, I)` means exactly that `I` is contained in the
Jacobson radical of `A`, expressed canonically as `I ≤ Ring.jacobson A`. -/
@[stacks 0ELY "Definition 15.10.1"]
#check (I ≤ Ring.jacobson A)

end
