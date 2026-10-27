/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.CategoryTheory.Fibered.InSets.Slice
public import ReasLib.CategoryTheory.Fibered.Stack.InSetsOver
public import ReasLib.CategoryTheory.Fibered.Stack.Prestack
import Mathlib.Tactic.CrossRefAttribute

/-!
# Representable slice stacks

This leaf owns the site-theoretic criterion for the canonical slice projection.  It is separate
from the chapter entries so localization arguments can use the criterion without importing a
chapter proof file.
-/

@[expose] public section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace Over

/-- Lemma 8.13.1 (tag 04WU), prestack refinement: the slice projection is a prestack exactly when
the represented presheaf is separated. -/
@[stacks 04WU "representable prestack criterion"]
theorem PrestackOnSite.iff_isSeparated
    (J : GrothendieckTopology C) (U : C) :
    IsPrestack.OnSite J (Over.forget U) ↔
      Presheaf.IsSeparated J (yoneda.obj U) := sorry

/-- Lemma 8.13.1 (tag 04WU): the slice projection is a stack exactly when the represented
presheaf is a sheaf. -/
@[stacks 04WU]
theorem StackOnSite.iff_isSheaf
    (J : GrothendieckTopology C) (U : C) :
    IsStack.OnSite J (Over.forget U) ↔ Presheaf.IsSheaf J (yoneda.obj U) := sorry

/-- Lemma 8.13.1 (tag 04WU), set-valued refinement: the slice projection is a stack in sets
exactly when the represented presheaf is a sheaf.

The discrete-fibration part is canonical, so the site-dependent content is precisely the ordinary
stack condition. -/
@[stacks 04WU "representable stack-in-sets criterion"]
theorem StackInSets.iff_isSheaf
    (J : GrothendieckTopology C) (U : C) :
    IsStack.InSets J (Over.forget U) ↔ Presheaf.IsSheaf J (yoneda.obj U) := by
  constructor
  · intro h
    apply (StackOnSite.iff_isSheaf J U).1
    exact { toIsFibered := inferInstance, toIsStack := h.toIsStack }
  · intro h
    exact {
      toIsDiscreteFibration := inferInstance
      toIsStack := ((StackOnSite.iff_isSheaf J U).2 h).toIsStack }

/-- Lemma 8.13.1 (tag 04WU), data owner: the canonical stack represented by a slice object whose
representable presheaf is a sheaf.

The root owner is a `StackOver.Sets`: the groupoid-fibred, setoid-fibred, and ordinary stack
presentations are its forgetful views rather than parallel constructions. -/
@[stacks 04WU "representable stack owner"]
def representableStack
    (J : GrothendieckTopology C) (U : C)
    (hU : Presheaf.IsSheaf J (yoneda.obj U)) :
    StackOver.Sets.{u, v, max u v, v} J :=
  StackOver.Sets.mk (FiberedCategoryOver.Sets.slice U)
    ((StackOnSite.iff_isSheaf J U).2 hU)

namespace representableStack

/-- The total category of the canonical representable stack is the ordinary slice category. -/
@[simp, stacks 04WU "representable set-stack total category"]
theorem total
    (J : GrothendieckTopology C) (U : C)
    (hU : Presheaf.IsSheaf J (yoneda.obj U)) :
    (representableStack J U hU).total = Over U := rfl

/-- The projection of the canonical representable stack is the ordinary slice-forget functor. -/
@[simp, stacks 04WU "representable set-stack projection"]
theorem p
    (J : GrothendieckTopology C) (U : C)
    (hU : Presheaf.IsSheaf J (yoneda.obj U)) :
    (representableStack J U hU).p = Over.forget U := rfl

/-- Forgetting the stack condition from the representable stack recovers the canonical set-fibred
slice. -/
@[simp, stacks 04WU "representable stack set-fibred view"]
theorem toSets
    (J : GrothendieckTopology C) (U : C)
    (hU : Presheaf.IsSheaf J (yoneda.obj U)) :
    (representableStack J U hU).toSets =
      FiberedCategoryOver.Sets.slice U := rfl

/-- Forgetting to the groupoid-fibred owner recovers the canonical groupoid-fibred slice. -/
@[simp, stacks 04WU "representable stack groupoid-fibred view"]
theorem toGroupoids
    (J : GrothendieckTopology C) (U : C)
    (hU : Presheaf.IsSheaf J (yoneda.obj U)) :
    (representableStack J U hU).toGroupoids.toGroupoids =
      FiberedCategoryOver.Groupoids.slice U := rfl

/-- The ordinary-stack view of the canonical representable stack. -/
@[stacks 04WU "representable ordinary-stack view"]
noncomputable abbrev stack
    (J : GrothendieckTopology C) (U : C)
    (hU : Presheaf.IsSheaf J (yoneda.obj U)) :
    StackOver.{u, v, max u v, v} J :=
  (representableStack J U hU).toStackOver

namespace stack

/-- The total category of the ordinary representable-stack view is the slice category. -/
@[simp, stacks 04WU "representable ordinary-stack total category"]
theorem total
    (J : GrothendieckTopology C) (U : C)
    (hU : Presheaf.IsSheaf J (yoneda.obj U)) :
    (stack J U hU).total = Over U := rfl

/-- The projection of the ordinary representable-stack view is the canonical slice projection. -/
@[simp, stacks 04WU "representable ordinary-stack projection"]
theorem p
    (J : GrothendieckTopology C) (U : C)
    (hU : Presheaf.IsSheaf J (yoneda.obj U)) :
    (stack J U hU).p = Over.forget U := rfl

/-- The projection of the representable stack is a discrete fibration. This is the strongest
canonical fibre property of a representable slice. -/
@[stacks 04WU "representable stack discrete-fibration instance"]
instance projectionInSets
    (J : GrothendieckTopology C) (U : C)
    (hU : Presheaf.IsSheaf J (yoneda.obj U)) :
    Functor.IsDiscreteFibration (stack J U hU).p :=
  Over.forgetIsDiscreteFibration U

end stack

end representableStack

end Over

end CategoryTheory
