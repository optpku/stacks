/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.StrictSlice.Construction
public import ReasLib.CategoryTheory.Fibered.Representable.Stack
public import ReasLib.CategoryTheory.Fibered.Stack.InheritedTopology.Over
import Mathlib.Tactic.CrossRefAttribute

/-!
# Basic presentations of stacks over a slice

This file owns the three bicategories used in localization over a representable object:
stacks on the slice site, the corresponding full subbicategory of a neutral strict slice,
and the strict slice internal to stacks.  It also exposes the projections from the neutral
presentation that do not depend on a sheaf witness for the representing object.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace StackOver.Localization

variable {J : GrothendieckTopology C}

set_option linter.checkUnivs false in
/-- The bicategory of stacks over the slice site `(C/U, J.over U)`.  The
topology is explicit because it is not determined by `U`. -/
@[stacks 04WV "stacks on a slice site"]
abbrev Localized (J : GrothendieckTopology C) (U : C) :=
  StackOver.{max u v, v, max u v, v} (J.over U)

/-- The property that the domain of a strict-slice object over the canonical
slice fibration is a stack on `(C, J)`. -/
@[stacks 04WV "stack-domain property for the neutral strict slice"]
def overSliceProperty (J : GrothendieckTopology C) (U : C) :
    ObjectProperty
      (StrictSlice (FiberedCategoryOver.ofFunctor (Over.forget U))) :=
  (IsStack.OnSite.objectProperty J).strictSlice
    (FiberedCategoryOver.ofFunctor (Over.forget U))

/-- The bicategory of stacks on `(C, J)` equipped with a strict structural map
to the canonical slice fibration represented by `U`.

The sheaf condition on `yoneda.obj U` is needed to regard the target itself as
a stack, but it does not determine this carrier and is therefore not a forced
parameter of `OverSlice`. -/
@[stacks 04WV "neutral strict-slice presentation"]
abbrev OverSlice (J : GrothendieckTopology C) (U : C) :=
  (overSliceProperty J U).FullSubbicategory

/-- The strict slice of the bicategory of stacks over the stack represented by `U`.

Unlike `OverSlice`, this presentation stores the structural morphism directly in
`StackOver J`. The sheaf witness is therefore part of the target object. -/
@[stacks 04WV "strict slice over a representable stack"]
noncomputable abbrev StackSlice
    (J : GrothendieckTopology C) (U : C)
    (hU : Presheaf.IsSheaf J (yoneda.obj U)) :=
  Bicategory.StrictSlice (Over.representableStack.stack J U hU)

namespace OverSlice

/-- Forget the stack condition on the domain of an object of `OverSlice`. -/
@[stacks 04WV "underlying fibred strict-slice object"]
abbrev toFiberedSlice {U : C} (X : OverSlice J U) :
    StrictSlice (FiberedCategoryOver.ofFunctor (Over.forget U)) :=
  X.1

/-- The domain of an `OverSlice` object, bundled as a stack on `(C, J)`. -/
@[stacks 04WV "stack domain of a neutral strict-slice object"]
def stack {U : C} (X : OverSlice J U) :
    StackOver.{u, v, max u v, v} J :=
  StackOver.mk X.toFiberedSlice.obj X.property

end OverSlice

/- The three carriers are canonical owners.  `OverSlice.stack` only re-bundles the domain
and its existing stack witness; it does not choose any mathematical data. -/

end StackOver.Localization

end CategoryTheory
