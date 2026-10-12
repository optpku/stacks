/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.Groupoid
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Basic

/-!
# Fibers of categories fibred in groupoids

Groupoid structures on standard fibers and the converse fiberwise recognition API for the
intrinsic owner `Functor.IsFibered.InGroupoids`.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Functor Functor.Fiber IsHomLift IsStronglyCartesian

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]

namespace Functor.IsFibered.InGroupoids

variable {p : S ⥤ C} [Functor.IsFibered.InGroupoids p]

/-- Every morphism in a standard fiber of a category fibred in groupoids is an isomorphism. -/
theorem hom_isIso (U : C) {X Y : p.Fiber U} (φ : X ⟶ Y) : IsIso φ := sorry

/-- Every standard fiber of a category fibred in groupoids is a groupoid. -/
instance fiberIsGroupoid (U : C) : IsGroupoid (p.Fiber U) := sorry

end Functor.IsFibered.InGroupoids

namespace Functor.IsFibered

/-- If a fibred functor has groupoid fibres, every total morphism is strongly Cartesian over its
image. -/
theorem isStronglyCartesian_of_fibersGroupoid
    {p : S ⥤ C} [p.IsFibered]
    (hfiber : ∀ U : C, IsGroupoid (p.Fiber U))
    {x y : S} (φ : x ⟶ y) :
    p.IsStronglyCartesian (p.map φ) φ := sorry

namespace InGroupoids

/-- A fibred functor whose standard fibres are groupoids is fibred in groupoids. -/
theorem of_isFibered_fibersGroupoid
    (p : S ⥤ C) (hp : p.IsFibered)
    (hfiber : ∀ U : C, IsGroupoid (p.Fiber U)) :
    Functor.IsFibered.InGroupoids p := sorry

/-- A functor is fibred in groupoids exactly when it is fibred and all its standard fibres are
groupoids. -/
theorem iff_isFibered_fibersGroupoid (p : S ⥤ C) :
    Functor.IsFibered.InGroupoids p ↔
      p.IsFibered ∧ ∀ U : C, IsGroupoid (p.Fiber U) := sorry

end InGroupoids
end Functor.IsFibered

end CategoryTheory
