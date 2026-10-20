/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap45.Lemma_45_7_1
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v w x

/- Lemma 45.9.1 (1): for a morphism `f : X ⟶ Y` of nonempty equidimensional
smooth projective schemes over `k`, data (D0), (D1), and (D3) satisfying
Poincaré duality (A) give the projection formula
`f₍*₎ (f⁎ b * a) = b * f₍*₎ a` on total Tate-twisted cohomology. -/
@[stacks 0FHB] #check
  (WeilCohomology.projectionFormula_of_indexedTrace :
    ∀ {V : Type u} [Category.{v} V] {F : Type w} [Field F] [CharZero F]
      (H : V → Type x) [∀ T, Ring (H T)] [∀ T, Algebra F (H T)]
      (pullback : ∀ {S T : V}, (S ⟶ T) → H T →ₐ[F] H S)
      (IsNonemptyEquidimensional : V → ℕ → Prop)
      (integral : ∀ {T : V} {d : ℕ},
        IsNonemptyEquidimensional T d → H T →ₗ[F] F)
      (pushforward : ∀ {S T : V} {d e : ℕ},
        IsNonemptyEquidimensional S d → IsNonemptyEquidimensional T e →
          (S ⟶ T) → H S →ₗ[F] H T)
      (pushforward_adjoint : ∀ {S T : V} {d e : ℕ}
        (hS : IsNonemptyEquidimensional S d) (hT : IsNonemptyEquidimensional T e)
        (f : S ⟶ T) (b : H T) (a : H S),
        integral hS (pullback f b * a) = integral hT (b * pushforward hS hT f a))
      (poincare_separates : ∀ {T : V} {d : ℕ}
        (hT : IsNonemptyEquidimensional T d) (a b : H T),
        (∀ c : H T, integral hT (c * a) = integral hT (c * b)) → a = b)
      {X Y : V} {d e : ℕ} (hX : IsNonemptyEquidimensional X d)
      (hY : IsNonemptyEquidimensional Y e) (f : X ⟶ Y) (b : H Y) (a : H X),
      pushforward hX hY f (pullback f b * a) = b * pushforward hX hY f a)

/- Lemma 45.9.1 (2): for composable morphisms `f : X ⟶ Y` and `g : Y ⟶ Z`
of nonempty equidimensional smooth projective schemes over `k`, data (D0),
(D1), and (D3) satisfying Poincaré duality (A) give
`g₍*₎ ∘ f₍*₎ = (f ≫ g)₍*₎` on total Tate-twisted cohomology. -/
@[stacks 0FHB] #check
  (WeilCohomology.pushforward_comp_of_indexedTrace :
    ∀ {V : Type u} [Category.{v} V] {F : Type w} [Field F] [CharZero F]
      (H : V → Type x) [∀ T, Ring (H T)] [∀ T, Algebra F (H T)]
      (pullback : ∀ {S T : V}, (S ⟶ T) → H T →ₐ[F] H S)
      (IsNonemptyEquidimensional : V → ℕ → Prop)
      (integral : ∀ {T : V} {d : ℕ},
        IsNonemptyEquidimensional T d → H T →ₗ[F] F)
      (pushforward : ∀ {S T : V} {d e : ℕ},
        IsNonemptyEquidimensional S d → IsNonemptyEquidimensional T e →
          (S ⟶ T) → H S →ₗ[F] H T)
      (pullback_comp : ∀ {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z),
        pullback (f ≫ g) = (pullback f).comp (pullback g))
      (pushforward_adjoint : ∀ {S T : V} {d e : ℕ}
        (hS : IsNonemptyEquidimensional S d) (hT : IsNonemptyEquidimensional T e)
        (f : S ⟶ T) (b : H T) (a : H S),
        integral hS (pullback f b * a) = integral hT (b * pushforward hS hT f a))
      (poincare_separates : ∀ {T : V} {d : ℕ}
        (hT : IsNonemptyEquidimensional T d) (a b : H T),
        (∀ c : H T, integral hT (c * a) = integral hT (c * b)) → a = b)
      {X Y Z : V} {d e n : ℕ} (hX : IsNonemptyEquidimensional X d)
      (hY : IsNonemptyEquidimensional Y e) (hZ : IsNonemptyEquidimensional Z n)
      (f : X ⟶ Y) (g : Y ⟶ Z),
      (pushforward hY hZ g).comp (pushforward hX hY f) =
        pushforward hX hZ (f ≫ g))
