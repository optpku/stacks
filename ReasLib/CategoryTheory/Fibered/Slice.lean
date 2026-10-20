/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import ReasLib.CategoryTheory.Fibered.InGroupoids
import Mathlib.Tactic.CrossRefAttribute

/-!
# Reflecting fibred structure through a slice projection

Fibredness and fibredness in groupoids can be reflected from
`p ⋙ Over.forget U : S ⥤ C` back to `p : S ⥤ Over U`.  The statements are specific to the slice
forgetful functor: their proofs use the commutative-triangle condition in `Over U`.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]

/-- A morphism over `Over U` that is strongly cartesian after applying `Over.forget U` is strongly
cartesian before forgetting. -/
instance isStronglyCartesian_of_comp_over_forget
    {U : C} (p : S ⥤ Over U)
    {a b : S} {A : Over U} {f : A ⟶ p.obj a} {φ : b ⟶ a}
    [(p ⋙ Over.forget U).IsStronglyCartesian f.left φ] :
    p.IsStronglyCartesian f φ := sorry
/- Proof strategy: reconstruct the slice-level lift equation from the forgotten equation using
`Over.eqToHom_left` and `Over.OverMorphism.ext`, then transfer the existence and uniqueness clauses
of the strongly cartesian universal property. -/

/-- If a functor to a slice becomes fibred after applying the slice forgetful functor, then it is
already fibred over the slice. -/
instance isFibered_of_comp_over_forget
    {U : C} (p : S ⥤ Over U)
    [(p ⋙ Over.forget U).IsFibered] :
    p.IsFibered := sorry
/- Proof strategy: choose a cartesian lift for the forgotten projection, upgrade it to a strongly
cartesian lift, reflect that structure with
`isStronglyCartesian_of_comp_over_forget`, and apply
`IsFibered.of_exists_isStronglyCartesian`. -/

/-- If a functor to a slice becomes fibred in groupoids after forgetting to the base, then every
standard fibre over a slice object is a groupoid. -/
instance IsFibered.InGroupoids.compOverForget.fiberIsGroupoid
    {U : C} (p : S ⥤ Over U)
    [Functor.IsFibered.InGroupoids (p ⋙ Over.forget U)]
    (A : Over U) :
    IsGroupoid (p.Fiber A) := sorry
/- Proof strategy: regard a vertical morphism over `A` as a morphism in the fibre of the composite
over `A.left`.  It is invertible there, and its inverse remains vertical in `Over U` by the slice
morphism extensionality theorem. -/

/-- Lemma 4.35.13 (Stacks 02XT): fibredness in groupoids reflects from a composite with the slice
forgetful functor. -/
@[stacks 02XT "groupoid-fibredness reflects along the slice forgetful functor", instance]
theorem IsFibered.InGroupoids.of_compOverForget
    {U : C} (p : S ⥤ Over U)
    [Functor.IsFibered.InGroupoids (p ⋙ Over.forget U)] :
    Functor.IsFibered.InGroupoids p := sorry
/- Proof strategy: use `isFibered_of_comp_over_forget` for fibredness and
`IsFibered.InGroupoids.compOverForget.fiberIsGroupoid` for every standard fibre, then apply
`IsFibered.InGroupoids.of_isFibered_fibersGroupoid`. -/

end CategoryTheory.Functor
