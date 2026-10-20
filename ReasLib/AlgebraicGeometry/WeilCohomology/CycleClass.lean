/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.GradedAlgebra.AlgHom
public import Mathlib.Algebra.Category.Ring.Basic

@[expose] public section

open CategoryTheory

universe u v w x

namespace WeilCohomology

/-- A pullback-natural family of graded homomorphisms from integral Chow rings to
the diagonal part of a cohomology theory. -/
structure CycleClass
    {C : Type u} [Category.{v} C]
    (CH₀ : C → Type w) [∀ X, CommRing (CH₀ X)]
    (CHgrade : ∀ X, ℤ → Submodule ℤ (CH₀ X))
    [∀ X, GradedAlgebra (CHgrade X)]
    (cyclePullback : ∀ {X Y : C}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X)
    (H : Cᵒᵖ ⥤ RingCat.{x})
    (Hdiag : ∀ X, ℕ → Submodule ℤ (H.obj (Opposite.op X))) where
  /-- The graded cycle-class homomorphism on an object. -/
  app : ∀ X, (fun i : ℕ ↦ CHgrade X (i : ℤ)) →+*ᵍ Hdiag X
  /-- Cycle classes commute with pullback. -/
  naturality : ∀ {X Y : C} (f : X ⟶ Y) (z : CH₀ Y),
    app X (cyclePullback f z) = H.map f.op (app Y z)

namespace CycleClass

variable {C : Type u} [Category.{v} C]
variable (CH₀ : C → Type w) [∀ X, CommRing (CH₀ X)]
variable (CHgrade : ∀ X, ℤ → Submodule ℤ (CH₀ X))
variable [∀ X, GradedAlgebra (CHgrade X)]
variable (cyclePullback : ∀ {X Y : C}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X)
variable (H : Cᵒᵖ ⥤ RingCat.{x})
variable (Hdiag : ∀ X, ℕ → Submodule ℤ (H.obj (Opposite.op X)))

/-- Construct a cycle-class rule from an explicit family of integral graded maps and its
pullback law. -/
def ofLaws
    (app : ∀ X, (fun i : ℕ ↦ CHgrade X (i : ℤ)) →+*ᵍ Hdiag X)
    (naturality : ∀ {X Y : C} (f : X ⟶ Y) (z : CH₀ Y),
      app X (cyclePullback f z) = H.map f.op (app Y z)) :
    CycleClass CH₀ CHgrade cyclePullback H Hdiag where
  app := app
  naturality := naturality

/-- Two cycle-class rules are equal when their objectwise graded ring
homomorphisms agree. -/
theorem ext
    (gamma gamma' : CycleClass CH₀ CHgrade cyclePullback H Hdiag)
    (h : ∀ X, gamma.app X = gamma'.app X) : gamma = gamma' := sorry

end CycleClass

end WeilCohomology
