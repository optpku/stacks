/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Iso
import StacksCheckRecall

@[expose] public section


universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {X Y : C}
variable (f : X ⟶ Y)

/- The source fixes a morphism `f : X ⟶ Y` and asks for a two-sided inverse. Although `Iso X Y`
is the bundled owner tagged `0017`, `IsIso f` is the exact unbundled proposition: its `out` field
is `∃ g : Y ⟶ X, f ≫ g = 𝟙 X ∧ g ≫ f = 𝟙 Y`. There is no generalization; Lean's diagrammatic
composition order translates the source equations directly. Recalling `IsIso` keeps the given
morphism visible, exposes the downstream `inv` and `asIso` API, and avoids treating its constructor
and projection as independent source clauses. -/

/- Definition 4.2.4: a morphism in a category is an isomorphism precisely when it admits a
two-sided inverse. This source notion is the canonical mathlib predicate `IsIso`. -/
@[stacks 0017 "invertible morphism"]
#check (IsIso f : Prop)

end CategoryTheory
