module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.StrictSlice.Equivalence
public import ReasLib.CategoryTheory.Fibered.Stack.Slice.Presentation.Computations
import Mathlib.Tactic.CrossRefAttribute

/-!
# Equivalence of the two strict-slice presentations

The two canonical repackaging strict pseudofunctors are strict inverses.  This file exports
the strict-inverse statement and the resulting biequivalence instances.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace StackOver.Localization

variable {J : GrothendieckTopology C}

namespace StackSlice

/-- The internal stack slice and the full subbicategory of the neutral slice are strict
inverses on objects, morphisms, and `2`-morphisms. -/
@[stacks 04WV "stack-slice presentation inverse"]
theorem isStrictInverse
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U)) :
    StrictPseudofunctor.IsStrictInverse
      (toOverSlice hU) (OverSlice.toStackSlice hU) := sorry

namespace toOverSlice

/-- Forgetting an internal stack slice to its ambient presentation is a biequivalence. -/
@[stacks 04WV "stack-slice to neutral-slice biequivalence"]
instance isBiequivalence
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U)) :
    Pseudofunctor.IsBiequivalence
      (StackSlice.toOverSlice hU).toPseudofunctor := sorry

end toOverSlice

end StackSlice

namespace OverSlice.toStackSlice

/-- Repackaging an ambient slice object as an internal stack slice is a biequivalence. -/
@[stacks 04WV "neutral-slice to stack-slice biequivalence"]
instance isBiequivalence
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U)) :
    Pseudofunctor.IsBiequivalence
      (OverSlice.toStackSlice hU).toPseudofunctor := sorry

end OverSlice.toStackSlice

end StackOver.Localization

end CategoryTheory
