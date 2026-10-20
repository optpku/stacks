/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.CategoryTheory.Category.Basic

@[expose] public section

open CategoryTheory

universe u v w x

namespace WeilCohomology

/-- Pulling the product of the two projection pullbacks back along a diagonal
is multiplication in the original algebra. -/
theorem cupProduct_eq_diagonal_pullback
    {V : Type u} [Category.{v} V] {F : Type w} [Field F]
    (H : V → Type x) [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    (product : V → V → V)
    (fst : ∀ X Y, product X Y ⟶ X) (snd : ∀ X Y, product X Y ⟶ Y)
    (diagonal : ∀ X, X ⟶ product X X)
    (pullback : ∀ {X Y}, (X ⟶ Y) → H Y →ₐ[F] H X)
    (diagonal_fst : ∀ X, diagonal X ≫ fst X X = 𝟙 X)
    (diagonal_snd : ∀ X, diagonal X ≫ snd X X = 𝟙 X)
    (pullback_id : ∀ X, pullback (𝟙 X) = AlgHom.id F (H X))
    (pullback_comp : ∀ {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z),
      pullback (f ≫ g) = (pullback f).comp (pullback g))
    (X : V) (a b : H X) :
    pullback (diagonal X)
        (pullback (fst X X) a * pullback (snd X X) b) = a * b := sorry

/-- Under compatibility with pullback and the diagonal formulas for intersection and
exterior products, preservation of intersection products by cycle classes is equivalent
to preservation of exterior products. -/
theorem cycleClass_preserves_mul_iff_externalProduct
    {V : Type u} [Category.{v} V] {F : Type w} [Field F]
    (CH : V → Type x) (H : V → Type x)
    [∀ X, CommRing (CH X)] [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
    (product : V → V → V)
    (fst : ∀ X Y, product X Y ⟶ X) (snd : ∀ X Y, product X Y ⟶ Y)
    (diagonal : ∀ X, X ⟶ product X X)
    (cyclePullback : ∀ {X Y}, (X ⟶ Y) → CH Y →+* CH X)
    (cohomologyPullback : ∀ {X Y}, (X ⟶ Y) → H Y →ₐ[F] H X)
    (cycleClass : ∀ X, CH X →+ H X)
    (externalProduct : ∀ {X Y}, CH X → CH Y → CH (product X Y))
    (diagonal_fst : ∀ X, diagonal X ≫ fst X X = 𝟙 X)
    (diagonal_snd : ∀ X, diagonal X ≫ snd X X = 𝟙 X)
    (cohomologyPullback_id : ∀ X,
      cohomologyPullback (𝟙 X) = AlgHom.id F (H X))
    (cohomologyPullback_comp : ∀ {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z),
      cohomologyPullback (f ≫ g) =
        (cohomologyPullback f).comp (cohomologyPullback g))
    (cycleClass_pullback : ∀ {X Y} (f : X ⟶ Y) (α : CH Y),
      cycleClass X (cyclePullback f α) = cohomologyPullback f (cycleClass Y α))
    (intersection_eq_diagonal_pullback : ∀ (X) (α β : CH X),
      α * β = cyclePullback (diagonal X) (externalProduct α β))
    (externalProduct_eq_mul_pullback : ∀ {X Y} (α : CH X) (β : CH Y),
      externalProduct α β = cyclePullback (fst X Y) α * cyclePullback (snd X Y) β) :
    (∀ (X) (α β : CH X), cycleClass X (α * β) = cycleClass X α * cycleClass X β) ↔
      ∀ (X Y) (α : CH X) (β : CH Y),
        cycleClass (product X Y) (externalProduct α β) =
          cohomologyPullback (fst X Y) (cycleClass X α) *
            cohomologyPullback (snd X Y) (cycleClass Y β) := sorry

end WeilCohomology
