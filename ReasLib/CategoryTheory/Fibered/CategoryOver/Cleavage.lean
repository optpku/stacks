module

public import ReasLib.CategoryTheory.Fibered.CategoryOver.Bicategory
public import ReasLib.CategoryTheory.Fibered.Cleavage.Basic.Intrinsic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cleavages of bundled fibred categories

This file exposes the choice of cartesian lifts directly from the fibredness witness stored by a
`FiberedCategoryOver`. It avoids rebuilding that witness through a separate typeclass theorem
before making a non-Prop choice.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver

/-- A cleavage selected directly from the fibredness witness stored in `X`. This is the named
choice boundary for constructions that require actual cartesian lifts from a bundled owner. -/
@[stacks 02XN "chosen cleavage of a bundled fibred category"]
noncomputable def chosenCleavage (X : FiberedCategoryOver.{u, v, w, vS} C) :
    X.p.Cleavage :=
  @Functor.Cleavage.ofIsFibered C _ X.total _ X.p X.property

end FiberedCategoryOver

end CategoryTheory
