/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Order.Directed
import StacksCheckRecall

@[expose] public section

universe u

/- Mathlib's `Preorder` and `PartialOrder` exactly own the reflexive/transitive and
antisymmetric relation data, while `Nonempty I ∧ IsDirectedOrder I` exactly expresses the two
extra conditions in each directed-set clause. The tagged `Preorder.smallCategory` is only the
downstream thin-category instance, and `CategoryTheory.IsFiltered` is only the resulting
categorical view, so neither should replace the source order-theoretic definition. There is no
generalization: the checks occur under `[Preorder I]` and `[PartialOrder I]`, respectively.
Using the standard owners introduces no wrapper and preserves ordinary typeclass reuse. -/

variable (I : Type u)

section

variable [Preorder I]

/- Definition 4.21.1 (1): a preorder, and hence a preordered set, is exactly the canonical
structure consisting of a reflexive and transitive relation `≤`. -/
@[stacks 00D3 "reflexive transitive relations and preordered sets"]
#check (inferInstance : Preorder I)

/- Definition 4.21.1 (2): a directed set is a preordered type whose carrier is nonempty and in
which every pair of elements has a common upper bound. -/
@[stacks 00D3 "nonempty directed preorders with common upper bounds"]
#check (Nonempty I ∧ IsDirectedOrder I)

end

section

variable [PartialOrder I]

/- Definition 4.21.1 (3): a partial order, and hence a partially ordered set, is exactly a
preorder whose relation `≤` is antisymmetric. -/
@[stacks 00D3 "antisymmetric preorders and partially ordered sets"]
#check (inferInstance : PartialOrder I)

/- Definition 4.21.1 (4): a directed partially ordered set is a partially ordered type whose
carrier is nonempty and whose elements have pairwise common upper bounds. -/
@[stacks 00D3 "nonempty directed partially ordered sets"]
#check (Nonempty I ∧ IsDirectedOrder I)

end
