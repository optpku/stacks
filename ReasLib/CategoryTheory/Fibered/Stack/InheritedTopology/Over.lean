/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Over
public import ReasLib.CategoryTheory.Fibered.Slice
public import ReasLib.CategoryTheory.Fibered.Stack.InheritedTopology.Composition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stack conditions over a slice site

For a representable sheaf `yoneda.obj U`, the stack condition over the slice topology `J.over U`
is equivalent to the stack condition obtained after composing with `Over.forget U`. The reverse
direction only uses separatedness of the representable presheaf. These projection-level owners
are independent of bundled `StackOver` objects and strict-slice presentations.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory.IsStack.OnSite.Over

variable {C : Type u} [Category.{v} C]
variable {S : Type w} [Category.{vS} S]
variable {J : GrothendieckTopology C} {U : C}

/-- For a representable sheaf, being a stack over the slice topology is equivalent to being a
stack over the original site after composing with the slice forgetful functor. -/
@[stacks 09WX "slice-site stack condition comparison"]
theorem iff_comp_forget
    (hU : Presheaf.IsSheaf J (yoneda.obj U)) (q : S ⥤ Over U) :
    IsStack.OnSite (J.over U) q ↔ IsStack.OnSite J (q ⋙ Over.forget U) := sorry

/-- A stack over the slice site remains a stack after composition with `Over.forget U`. -/
@[stacks 09WX "slice-site stack composition"]
theorem comp_forget
    (hU : Presheaf.IsSheaf J (yoneda.obj U)) (q : S ⥤ Over U)
    [IsStack.OnSite (J.over U) q] :
    IsStack.OnSite J (q ⋙ Over.forget U) := sorry

/-- A projection to `C/U` is a stack over the slice site when its composite with
`Over.forget U` is a stack over `(C, J)` and the represented presheaf is separated. -/
@[stacks 09WX]
theorem of_comp_forget
    (hU : Presheaf.IsSeparated J (yoneda.obj U)) (q : S ⥤ Over U)
    [IsStack.OnSite J (q ⋙ Over.forget U)] :
    IsStack.OnSite (J.over U) q := sorry

end CategoryTheory.IsStack.OnSite.Over
