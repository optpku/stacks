/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.36.1

@stack 00GI
-/

-- Declarations for this item will be appended below by the statement pipeline.

/-
Source/core/bridge triage:
* source-facing: integrality of an element and of a ring map in the textbook sense;
* core/canonical: the mathlib owner predicates `RingHom.IsIntegralElem` and
  `RingHom.IsIntegral`;
* bridge/view: the algebra-specialized predicate `IsIntegral`, obtained by applying
  `RingHom.IsIntegralElem` to `algebraMap`.

Primitive data here are only the ring map `φ : R →+* S` and the element `s : S`. The defining
polynomial witness is already part of the owner predicate, so keeping any local wrapper or
restatement would only duplicate existing public API.
-/

/- Definition 10.36.1 (1): for a ring map `φ : R →+* S`, an element `s : S` is integral over `R`
with respect to `φ` exactly in the canonical owner predicate `φ.IsIntegralElem s`, defined by the
existence of a monic polynomial `P : R[X]` with `eval₂ φ s P = 0`. -/
@[stacks 00GI "integral element"]
#check @RingHom.IsIntegralElem

/- Definition 10.36.1 (2): a ring map `φ : R →+* S` is integral exactly in the canonical owner
predicate `φ.IsIntegral`, i.e. every `s : S` satisfies `φ.IsIntegralElem s`. -/
@[stacks 00GI "integral ring map"]
#check @RingHom.IsIntegral
