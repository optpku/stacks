/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.AdjoinRoot
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial

noncomputable section

universe u

variable {k : Type u} [Field k]

/- 
Domain-style sampling for Example 9.3.3:
- primary domain: polynomial quotients and adjoining a root of an irreducible polynomial;
- sampled owner API:
  `AdjoinRoot`,
  `AdjoinRoot.span_maximal_of_irreducible`,
  `AdjoinRoot.instField`,
  `Ideal.Quotient.field`;
- best owner abstraction: the upstream instance
  `AdjoinRoot.instField : Field (AdjoinRoot P)`,
  used here through the definitional equality
  `AdjoinRoot P = k[X] ⧸ Ideal.span {P}`.

Primitive-vs-derived split:
- primitive data: the polynomial `P : k[X]` and the quotient ring `k[X] ⧸ Ideal.span {P}`;
- derived API: maximality of `(P)` under irreducibility and the induced field structure.

Source/core/bridge triage:
- `source-facing`: the textbook quotient-ring statement `k[X]/(P)` is a field for irreducible `P`;
- `core/canonical`: `AdjoinRoot.instField`;
- `bridge/view`: the quotient-ring type expression `k[X] ⧸ Ideal.span {P}`.

There is no extra local mathematics to package, so the file should check the canonical owner
instance directly rather than introduce a parallel local field construction.
-/
/-
Example 9.3.3: if `P : k[X]` is irreducible, then the quotient `k[X] ⧸ Ideal.span {P}`
is a field. This is the canonical `AdjoinRoot.instField` instance, definitionally on the same
quotient ring.
-/
@[stacks 09FI]
#check AdjoinRoot.instField
