/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Slice.Equivalence.Computations
public import ReasLib.CategoryTheory.Fibered.Stack.Slice.ExtendRestrict.Equivalence
public import ReasLib.CategoryTheory.Fibered.Stack.Slice.Presentation.Equivalence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Localization as a representable stack slice

The direct localization and restriction functors are strict inverses because each of their
extension/restriction and presentation-change factors is.  This file owns the final
strict-inverse statement and biequivalence instances.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace StackOver.Localization

variable {J : GrothendieckTopology C}

namespace Localized.stackSlice

/-- Localization and restriction give strict inverse pseudofunctors between stacks on the
slice site and the internal strict slice over the representable stack. -/
@[stacks 04WV "localization as a representable stack slice"]
theorem isStrictInverse
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U)) :
    StrictPseudofunctor.IsStrictInverse
      (Localized.toStackSlice hU) (StackSlice.toLocalized hU) := sorry

end Localized.stackSlice

namespace Localized.toStackSlice

/-- Direct localization into the representable stack slice is a biequivalence. -/
@[stacks 04WV "direct localization biequivalence"]
instance isBiequivalence
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U)) :
    Pseudofunctor.IsBiequivalence
      (Localized.toStackSlice hU).toPseudofunctor := sorry

end Localized.toStackSlice

namespace StackSlice.toLocalized

/-- Direct restriction from the representable stack slice is a biequivalence. -/
@[stacks 04WV "direct restriction biequivalence"]
instance isBiequivalence
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U)) :
    Pseudofunctor.IsBiequivalence
      (StackSlice.toLocalized hU).toPseudofunctor := sorry

end StackSlice.toLocalized

end StackOver.Localization

end CategoryTheory
