/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Final
import StacksCheckRecall

@[expose] public section

universe vI uI vJ uJ

namespace CategoryTheory.Functor

variable {I : Type uI} [Category.{vI} I]
variable {J : Type uJ} [Category.{vJ} J]
variable (H : I ⥤ J)

/- The source's pairs `(x, b : y ⟶ H.obj x)` and compatible arrows are exactly the objects and
morphisms of `StructuredArrow y H`. The verified owner `Functor.Final` requires each such category
to be `IsConnected`, which is precisely nonemptiness together with one zigzag equivalence class.
Thus a separate nonemptiness-and-zigzag theorem would duplicate the owner rather than provide a
distinct bridge. No generalization is introduced, and the recall exposes the standard final-functor
API for downstream colimit arguments. -/

/- Definition 4.17.1: a functor `H : I ⥤ J` is cofinal when every category
`StructuredArrow y H` is connected. -/
@[stacks 04E6 "cofinal functors via connected structured-arrow categories"]
#check (Final H : Prop)

end CategoryTheory.Functor
