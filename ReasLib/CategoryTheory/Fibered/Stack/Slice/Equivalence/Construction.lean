/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Slice.ExtendRestrict.Construction
public import ReasLib.CategoryTheory.Fibered.Stack.Slice.Presentation.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Direct localization as a representable stack slice

Composing extension with the presentation change gives direct strict pseudofunctors between
stacks on the slice site and the strict slice over the represented stack.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace StackOver.Localization

variable {J : GrothendieckTopology C}

namespace Localized

/-- Lemma 8.13.2 (tag 04WV), forward data: send a stack on the slice site directly to a stack over
`(C, J)` equipped with its structural morphism to the stack represented by `U`. -/
@[stacks 04WV "stack localization to representable stack slice"]
noncomputable def toStackSlice
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U)) :
    StrictPseudofunctor (Localized J U) (StackSlice J U hU) :=
  (Extend.functor hU).comp (OverSlice.toStackSlice hU)

end Localized

namespace StackSlice

/-- Lemma 8.13.2 (tag 04WV), inverse data: recover a stack on the slice site directly from a stack
equipped with a strict morphism to the stack represented by `U`. -/
@[stacks 04WV "representable stack slice to stack localization"]
noncomputable def toLocalized
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U)) :
    StrictPseudofunctor (StackSlice J U hU) (Localized J U) :=
  (toOverSlice hU).comp (Restrict.functor hU.isSeparated)

end StackSlice

/- Both functors are composites of existing explicit strict pseudofunctors; no object,
morphism, or `2`-morphism data is selected again here. -/

end StackOver.Localization

end CategoryTheory
