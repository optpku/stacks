/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Slice.Presentation.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Computation rules for the two strict-slice presentations

These lemmas expose the object, morphism, and `2`-morphism data retained by the canonical
repackaging functors between `StackSlice` and `OverSlice`.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace StackOver.Localization

variable {J : GrothendieckTopology C}

namespace StackSlice.toOverSlice

/-- On objects, forgetting the internal stack slice is the source-facing constructor from a
stack and its structural morphism. -/
@[simp, stacks 04WV "stack-slice object repackaging"]
theorem obj
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (X : StackSlice J U hU) :
    (StackSlice.toOverSlice hU).obj X =
      OverSlice.mk hU X.obj X.hom := sorry

/-- Forgetting an internal slice morphism retains its underlying fibred-category
morphism between the domain stacks. -/
@[simp, stacks 04WV "stack-slice morphism projection"]
theorem map.hom
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {X Y : StackSlice J U hU} (F : X ⟶ Y) :
    Bicategory.StrictSlice.Hom.hom ((StackSlice.toOverSlice hU).map F).hom =
      StackOver.Hom.toMor (Bicategory.StrictSlice.Hom.hom F) := sorry

/-- Forgetting an internal slice `2`-morphism retains its underlying
fibred-category `2`-morphism. -/
@[simp, stacks 04WV "stack-slice two-cell projection"]
theorem map₂.hom
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {X Y : StackSlice J U hU} {F G : X ⟶ Y} (eta : F ⟶ G) :
    Bicategory.StrictSlice.Hom₂.hom
        ((StackSlice.toOverSlice hU).map₂ eta).hom =
      StackOver.Hom.toMor₂ (Bicategory.StrictSlice.Hom₂.hom eta) := sorry

end StackSlice.toOverSlice

namespace OverSlice.toStackSlice

/-- The domain stack of the internal slice object reconstructed from `X` is `X.stack`. -/
@[simp, stacks 04WV "ambient-slice domain projection"]
theorem domain
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (X : OverSlice J U) :
    ((OverSlice.toStackSlice hU).obj X).obj = X.stack := sorry

/-- The structural morphism of the internal slice object reconstructed from `X` is the
canonical stack morphism `X.hom hU`. -/
@[simp, stacks 04WV "ambient-slice structural map projection"]
theorem arrow
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (X : OverSlice J U) :
    ((OverSlice.toStackSlice hU).obj X).hom = X.hom hU := sorry

/-- Repackaging an ambient slice morphism retains its underlying
fibred-category morphism. -/
@[simp, stacks 04WV "ambient-slice morphism projection"]
theorem map.hom
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {X Y : OverSlice J U} (F : X ⟶ Y) :
    StackOver.Hom.toMor
        (Bicategory.StrictSlice.Hom.hom
          ((OverSlice.toStackSlice hU).map F)) =
      Bicategory.StrictSlice.Hom.hom F.hom := sorry

/-- Repackaging an ambient slice `2`-morphism retains its underlying
fibred-category `2`-morphism. -/
@[simp, stacks 04WV "ambient-slice two-cell projection"]
theorem map₂.hom
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U))
    {X Y : OverSlice J U} {F G : X ⟶ Y} (eta : F ⟶ G) :
    StackOver.Hom.toMor₂
        (Bicategory.StrictSlice.Hom₂.hom
          ((OverSlice.toStackSlice hU).map₂ eta)) =
      Bicategory.StrictSlice.Hom₂.hom eta.hom := sorry

end OverSlice.toStackSlice

end StackOver.Localization

end CategoryTheory
