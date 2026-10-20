/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import StacksCheckRecall

@[expose] public section


universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {X : C}

/- The source gives the unique-morphism presentations. Mathlib's `IsInitial` and `IsTerminal`
are the canonical empty-colimit and empty-limit owners, while `isInitialEquivUnique` and
`isTerminalEquivUnique` recover those presentations literally. Choosing the owners introduces no
generalization, avoids parallel predicates, and exposes the standard downstream universal-property
API; the companion checks below record the exact source-facing equivalences. -/

/- Definition 4.12.1 (1): an object is initial exactly when it is an `IsInitial` object. -/
@[stacks 002C "initial object: a unique morphism to every object"]
#check (IsInitial X : Type (max u v))

/- Definition 4.12.1 (2): the source's final objects are mathlib's `IsTerminal` objects. -/
@[stacks 002C "final object: a unique morphism from every object"]
#check (IsTerminal X : Type (max u v))

/- Companion bridge: the textbook unique-morphism characterization of an initial object is the
canonical specialization of `isInitialEquivUnique` to the empty diagram. -/
#check (isInitialEquivUnique (Functor.empty C) X : IsInitial X ≃ ∀ Y, Unique (X ⟶ Y))

/- Companion bridge: the textbook unique-morphism characterization of a terminal object is the
canonical specialization of `isTerminalEquivUnique` to the empty diagram. -/
#check (isTerminalEquivUnique (Functor.empty C) X : IsTerminal X ≃ ∀ Y, Unique (Y ⟶ X))

end CategoryTheory.Limits
