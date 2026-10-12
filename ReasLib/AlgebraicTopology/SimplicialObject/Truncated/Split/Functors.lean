/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Split.Category
import Mathlib.Tactic.CrossRefAttribute

/-!
# Functors from split truncated simplicial objects

This module exposes the forgetful functor, distinguished-summand evaluation, and the natural
inclusions of summands into degrees.
-/

@[expose] public section

open CategoryTheory Opposite Simplicial
open scoped SimplexCategory.Truncated

universe v u

namespace CategoryTheory.SimplicialObject.Truncated.Split

/-- Forget the chosen splitting of a split truncated simplicial object. -/
@[stacks 017P "forgetful functor from split truncated simplicial objects"]
def forget (C : Type u) [Category.{v} C] {n : ℕ} :
    Split C n ⥤ SimplicialObject.Truncated C n where
  obj S := S.X
  map Φ := Φ.F

/-- The forgetful functor returns the underlying truncated simplicial object. -/
@[simp, stacks 017P "object map of the truncated split forgetful functor"]
theorem forget_obj {C : Type u} [Category.{v} C] {n : ℕ} (S : Split C n) :
    (forget C).obj S = S.X := sorry

/-- The forgetful functor returns the underlying truncated simplicial morphism. -/
@[simp, stacks 017P "morphism map of the truncated split forgetful functor"]
theorem forget_map {C : Type u} [Category.{v} C] {n : ℕ}
    {S₁ S₂ : Split C n} (Φ : S₁ ⟶ S₂) :
    (forget C).map Φ = Φ.F := sorry

/-- Evaluate a split truncated simplicial object at its distinguished summand in degree `m`. -/
@[stacks 017P "distinguished summand evaluation functor"]
def evalN (C : Type u) [Category.{v} C] {n : ℕ} (m : Fin (n + 1)) :
    Split C n ⥤ C where
  obj S := S.s.N m
  map Φ := Φ.f m

/-- Object formula for distinguished-summand evaluation. -/
@[simp, stacks 017P "object map of distinguished summand evaluation"]
theorem evalN_obj {C : Type u} [Category.{v} C] {n : ℕ}
    (m : Fin (n + 1)) (S : Split C n) :
    (evalN C m).obj S = S.s.N m := sorry

/-- Morphism formula for distinguished-summand evaluation. -/
@[simp, stacks 017P "morphism map of distinguished summand evaluation"]
theorem evalN_map {C : Type u} [Category.{v} C] {n : ℕ}
    (m : Fin (n + 1)) {S₁ S₂ : Split C n} (Φ : S₁ ⟶ S₂) :
    (evalN C m).map Φ = Φ.f m := sorry

/-- The coproduct injection of a fixed splitting index is natural in split truncated
simplicial objects. -/
@[stacks 017P "natural distinguished summand inclusion"]
def cofanInj (C : Type u) [Category.{v} C] {n : ℕ}
    {Δ : (SimplexCategory.Truncated n)ᵒᵖ} (A : Splitting.IndexSet Δ) :
    evalN C A.degree ⟶
      forget C ⋙ (evaluation (SimplexCategory.Truncated n)ᵒᵖ C).obj Δ where
  app S := (S.s.cofan Δ).inj A
  naturality _ _ Φ := (Hom.cofan_inj Φ A).symm

/-- Component formula for the natural distinguished-summand inclusion. -/
@[simp, stacks 017P "component of the natural distinguished summand inclusion"]
theorem cofanInj_app {C : Type u} [Category.{v} C] {n : ℕ}
    {Δ : (SimplexCategory.Truncated n)ᵒᵖ} (A : Splitting.IndexSet Δ)
    (S : Split C n) :
    (cofanInj C A).app S = (S.s.cofan Δ).inj A := sorry

end CategoryTheory.SimplicialObject.Truncated.Split
