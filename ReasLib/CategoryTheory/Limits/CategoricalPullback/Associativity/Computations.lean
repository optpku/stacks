/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Associativity.Basic

/-!
# Computations for categorical-pullback reassociation

Object and morphism projection formulas for the two explicit reassociation functors.
-/

@[expose] public section

open CategoryTheory.Limits
open scoped CategoricalPullback

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]
variable {C : Type u₃} [Category.{v₃} C]
variable {D : Type u₄} [Category.{v₄} D]
variable {E : Type u₅} [Category.{v₅} E]

namespace Limits.CategoricalPullback

variable (F : A ⥤ B) (G : C ⥤ B) (H : C ⥤ D) (I : E ⥤ D)

-- Local declaration justification (source-local notation): this file computes the fixed
-- endpoints of the reassociation equivalence supplied by `Associativity.Basic`. The names keep
-- those repeated endpoints readable; they do not define an independent public construction.
local notation "LeftAssociated" => (((π₂ F G) ⋙ H) ⊡ I)
-- Local declaration justification (source-local notation): this is the fixed right-associated
-- endpoint of the same reassociation computation and has no independent public operation.
local notation "RightAssociated" => (F ⊡ ((π₁ H I) ⋙ G))

namespace Associator.forward

/-- Forward reassociation retains the leftmost object. -/
@[simp]
theorem obj.fst (X : LeftAssociated) :
    ((Associator.forward F G H I).obj X).fst = X.fst.fst := sorry

/-- Forward reassociation retains the middle object. -/
@[simp]
theorem obj.sndFst (X : LeftAssociated) :
    ((Associator.forward F G H I).obj X).snd.fst = X.fst.snd := sorry

/-- Forward reassociation retains the rightmost object. -/
@[simp]
theorem obj.sndSnd (X : LeftAssociated) :
    ((Associator.forward F G H I).obj X).snd.snd = X.snd := sorry

/-- The inner structural isomorphism after forward reassociation is the original outer one. -/
@[simp]
theorem obj.sndIso (X : LeftAssociated) :
    ((Associator.forward F G H I).obj X).snd.iso = X.iso := sorry

/-- The outer structural isomorphism after forward reassociation is the original inner one. -/
@[simp]
theorem obj.iso (X : LeftAssociated) :
    ((Associator.forward F G H I).obj X).iso = X.fst.iso := sorry

/-- On morphisms, forward reassociation retains the leftmost component. -/
@[simp]
theorem hom.fst {X Y : LeftAssociated} (f : X ⟶ Y) :
    ((Associator.forward F G H I).map f).fst = f.fst.fst := sorry

/-- On morphisms, forward reassociation retains the middle component. -/
@[simp]
theorem hom.sndFst {X Y : LeftAssociated} (f : X ⟶ Y) :
    ((Associator.forward F G H I).map f).snd.fst = f.fst.snd := sorry

/-- On morphisms, forward reassociation retains the rightmost component. -/
@[simp]
theorem hom.sndSnd {X Y : LeftAssociated} (f : X ⟶ Y) :
    ((Associator.forward F G H I).map f).snd.snd = f.snd := sorry

end Associator.forward

namespace Associator.inverse

/-- Inverse reassociation retains the leftmost object. -/
@[simp]
theorem obj.fstFst (X : RightAssociated) :
    ((Associator.inverse F G H I).obj X).fst.fst = X.fst := sorry

/-- Inverse reassociation retains the middle object. -/
@[simp]
theorem obj.fstSnd (X : RightAssociated) :
    ((Associator.inverse F G H I).obj X).fst.snd = X.snd.fst := sorry

/-- The inner structural isomorphism after inverse reassociation is the original outer one. -/
@[simp]
theorem obj.fstIso (X : RightAssociated) :
    ((Associator.inverse F G H I).obj X).fst.iso = X.iso := sorry

/-- Inverse reassociation retains the rightmost object. -/
@[simp]
theorem obj.snd (X : RightAssociated) :
    ((Associator.inverse F G H I).obj X).snd = X.snd.snd := sorry

/-- The outer structural isomorphism after inverse reassociation is the original inner one. -/
@[simp]
theorem obj.iso (X : RightAssociated) :
    ((Associator.inverse F G H I).obj X).iso = X.snd.iso := sorry

/-- On morphisms, inverse reassociation retains the leftmost component. -/
@[simp]
theorem hom.fstFst {X Y : RightAssociated} (f : X ⟶ Y) :
    ((Associator.inverse F G H I).map f).fst.fst = f.fst := sorry

/-- On morphisms, inverse reassociation retains the middle component. -/
@[simp]
theorem hom.fstSnd {X Y : RightAssociated} (f : X ⟶ Y) :
    ((Associator.inverse F G H I).map f).fst.snd = f.snd.fst := sorry

/-- On morphisms, inverse reassociation retains the rightmost component. -/
@[simp]
theorem hom.snd {X Y : RightAssociated} (f : X ⟶ Y) :
    ((Associator.inverse F G H I).map f).snd = f.snd.snd := sorry

end Associator.inverse

end Limits.CategoricalPullback

end CategoryTheory
