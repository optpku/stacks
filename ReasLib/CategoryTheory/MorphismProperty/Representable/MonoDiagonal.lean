/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Representable

/-! # Representable diagonals of subobjects

A monomorphism into an object with a relatively representable diagonal inherits a
relatively representable diagonal. The representing object is the given ambient
diagonal pullback; the test map supplies its subobject projection.
-/

@[expose] public section

open CategoryTheory.Limits

noncomputable section

universe u₁ v₁ u₂ v₂

namespace CategoryTheory.Functor.relativelyRepresentable

/-- A subobject inherits the ambient represented diagonal, with the same test object
and an explicit universal lift. -/
theorem diagonal_of_mono {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) {U X : D}
    [HasBinaryProduct U U] [HasBinaryProduct X X] (i : U ⟶ X) [Mono i]
    (hX : F.relativelyRepresentable (Limits.diag X)) :
    F.relativelyRepresentable (Limits.diag U) := by
  intro T a
  let ambientTest : F.obj T ⟶ X ⨯ X := a ≫ prod.map i i
  let Q := hX.pullback ambientTest
  let snd : Q ⟶ T := hX.snd ambientTest
  let fst : F.obj Q ⟶ U := F.map snd ≫ a ≫ prod.fst
  let lift : ∀ c : PullbackCone (Limits.diag U) a, c.pt ⟶ F.obj Q := fun c ↦
    (hX.isPullback ambientTest).lift (c.fst ≫ i) c.snd sorry
  have condition : Mono i → fst ≫ Limits.diag U = F.map snd ≫ a := sorry
  have lift_fst : Mono i → ∀ c, lift c ≫ fst = c.fst := sorry
  have lift_snd : ∀ c, lift c ≫ F.map snd = c.snd := sorry
  have unique : Mono i → ∀ c (m : c.pt ⟶ F.obj Q),
      m ≫ fst = c.fst → m ≫ F.map snd = c.snd → m = lift c := sorry
  exact ⟨Q, snd, fst, IsPullback.of_isLimit
    (PullbackCone.IsLimit.mk (condition inferInstance) lift
      (lift_fst inferInstance) lift_snd (unique inferInstance))⟩

end CategoryTheory.Functor.relativelyRepresentable
