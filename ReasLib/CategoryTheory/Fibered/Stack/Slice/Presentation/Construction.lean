/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Slice.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Maps between the two strict-slice presentations

The internal strict slice in `StackOver J` and the full subbicategory of the neutral strict
slice carry the same data.  This file owns the two repackaging strict pseudofunctors and the
source-facing constructor and projections for the neutral presentation.
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

/-- Forget that the structural morphism lives in `StackOver J`, retaining the stack property
of its domain as a full-subbicategory witness in the neutral strict slice. -/
@[stacks 04WV "stack slice to neutral slice"]
noncomputable def toOverSlice
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U)) :
    StrictPseudofunctor (StackSlice J U hU) (OverSlice J U) :=
  ObjectProperty.FullSubbicategory.StrictSlice.toAmbient
    (IsStack.OnSite.objectProperty.{u, v, max u v, v} J)
    (Over.representableStack.stack J U hU)

end StackSlice

namespace OverSlice

/-- Repackage a neutral strict-slice object with stack domain as a strict-slice object in
`StackOver J`. -/
@[stacks 04WV "neutral slice to stack slice"]
noncomputable def toStackSlice
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U)) :
    StrictPseudofunctor (OverSlice J U) (StackSlice J U hU) :=
  ObjectProperty.FullSubbicategory.StrictSlice.ofAmbient
    (IsStack.OnSite.objectProperty.{u, v, max u v, v} J)
    (Over.representableStack.stack J U hU)

/-- When `yoneda.obj U` is a sheaf, the structural fibred-category morphism of
an `OverSlice` object lifts to a morphism of stacks. -/
@[stacks 04WV "stack-slice structural morphism"]
noncomputable def hom
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (X : OverSlice J U) :
    X.stack ⟶ Over.representableStack.stack J U hU :=
  ((toStackSlice hU).obj X).hom

/-- Package a stack and a structural morphism to the representable stack as
an object of the canonical full subbicategory `OverSlice J U`. -/
@[stacks 04WV "stack-slice object constructor"]
noncomputable def mk
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (X : StackOver.{u, v, max u v, v} J)
    (f : X ⟶ Over.representableStack.stack J U hU) : OverSlice J U :=
  (StackSlice.toOverSlice hU).obj (Bicategory.StrictSlice.mk X f)

/-- The underlying neutral strict-slice object of `mk hU X f` is the supplied
domain and structural morphism. -/
@[simp, stacks 04WV "stack-slice constructor underlying object"]
theorem mk.toFiberedSlice
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (X : StackOver.{u, v, max u v, v} J)
    (f : X ⟶ Over.representableStack.stack J U hU) :
    (mk hU X f).toFiberedSlice =
      StrictSlice.mk X.toFiberedCategoryOver (StackOver.Hom.toMor f) := sorry

/-- Rebundling the domain stack of `mk hU X f` recovers `X`. -/
@[simp, stacks 04WV "stack-slice constructor domain"]
theorem mk.stack
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (X : StackOver.{u, v, max u v, v} J)
    (f : X ⟶ Over.representableStack.stack J U hU) :
    (mk hU X f).stack = X := sorry

/-- The structural morphism reconstructed by `mk` is the supplied morphism,
after the canonical equality transport of its source stack. -/
@[simp, stacks 04WV "stack-slice constructor structural morphism"]
theorem mk.hom
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (X : StackOver.{u, v, max u v, v} J)
    (f : X ⟶ Over.representableStack.stack J U hU) :
    hom hU (mk hU X f) = eqToHom (mk.stack hU X f) ≫ f := sorry

/-- Repackaging the source-facing stack and structural morphism of an
`OverSlice` object recovers the canonical full-subbicategory owner. -/
@[simp, stacks 04WV "stack-slice constructor round trip"]
theorem mk.roundTrip
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (X : OverSlice J U) :
    mk hU X.stack (OverSlice.hom hU X) = X := sorry

/-- The ambient fibred-category morphism of the structural stack morphism is
the structural arrow stored by the neutral strict-slice owner. -/
@[simp, stacks 04WV "stack-slice structural morphism projection"]
theorem hom.toMor
    {U : C} (hU : Presheaf.IsSheaf J (yoneda.obj U))
    (X : OverSlice J U) :
    StackOver.Hom.toMor (hom hU X) = X.toFiberedSlice.hom := sorry

end OverSlice

end StackOver.Localization

end CategoryTheory
