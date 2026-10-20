/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.RingTheory.Noetherian.Defs
import StacksCheckRecall

/-!
# Definition 15.23.9

The reflexive hull is the canonical double dual.

@stack 0AV4
-/

@[expose] public section

universe u v

open Module

/-
Domain-style sampling:
- primary domain: module duality, double duals, and reflexivity for modules;
- sampled owner declarations:
  `Dual`,
  `Module.Dual.eval`,
  `Module.IsReflexive`,
  `Module.evalEquiv`;
- best owner abstraction: the source term "reflexive hull" is just the canonical double-dual
  owner type `Dual R (Dual R M)`;
- primitive data: the commutative semiring `R`, the additive commutative monoid `M`, and the
  ambient module structure;
- derived API: the surrounding evaluation and reflexivity statements are already owned by
  `Module.Dual.eval` and `Module.IsReflexive`.

Source/core/bridge triage:
- `source-facing`: the textbook phrase "the reflexive hull of `M`";
- `core/canonical`: the double-dual type `Dual R (Dual R M)`;
- `bridge/view`: later lemmas comparing `M` with its double dual through the evaluation map.

This item is therefore a pure canonical recall/check item, not a place for a new public alias.
-/

/- Definition 15.23.9: the textbook reflexive hull of `M` is the canonical double-dual
`R`-module `Hom_R(Hom_R(M, R), R)` for `M` finite over the Noetherian domain `R`. -/
@[stacks 0AV4 "Definition 15.23.9"]
#check fun (R : Type u) (M : Type v) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] => Dual R (Dual R M)

/- The double-dual type itself is available under the weaker canonical assumptions. -/
#check fun (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M] =>
  Dual R (Dual R M)
