/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u v w x

namespace WeilCohomology

variable {V : Type u} [Category.{v} V]
variable {F : Type w} [Field F] [CharZero F]
variable (H : V → Type x) [∀ X, Ring (H X)] [∀ X, Algebra F (H X)]
variable (pullback : ∀ {X Y : V}, (X ⟶ Y) → H Y →ₐ[F] H X)
variable (pushforward : ∀ {X Y : V}, (X ⟶ Y) → H X →ₗ[F] H Y)
variable (trace : ∀ X : V, H X →ₗ[F] F)

/-- A pushforward adjoint to pullback for a separating trace pairing satisfies the
projection formula. -/
theorem projectionFormula
    (pushforward_adjoint : ∀ {X Y : V} (f : X ⟶ Y) (b : H Y) (a : H X),
      trace X (pullback f b * a) = trace Y (b * pushforward f a))
    (poincare_separates : ∀ (X : V) (x y : H X),
      (∀ c : H X, trace X (c * x) = trace X (c * y)) → x = y)
    {X Y : V} (f : X ⟶ Y) (b : H Y) (a : H X) :
    pushforward f (pullback f b * a) = b * pushforward f a := sorry

/-- Pushforwards adjoint to a composition-compatible contravariant pullback are
compatible with composition when the trace pairing separates equality. -/
theorem pushforward_comp
    (pullback_comp : ∀ {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z),
      pullback (f ≫ g) = (pullback f).comp (pullback g))
    (pushforward_adjoint : ∀ {X Y : V} (f : X ⟶ Y) (b : H Y) (a : H X),
      trace X (pullback f b * a) = trace Y (b * pushforward f a))
    (poincare_separates : ∀ (X : V) (x y : H X),
      (∀ c : H X, trace X (c * x) = trace X (c * y)) → x = y)
    {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (pushforward g).comp (pushforward f) = pushforward (f ≫ g) := sorry

/-- A pushforward indexed by dimension witnesses and adjoint to pullback for the
corresponding separating trace pairing satisfies the projection formula. -/
theorem projectionFormula_of_indexedTrace
    (IsNonemptyEquidimensional : V → ℕ → Prop)
    (integral : ∀ {X : V} {d : ℕ},
      IsNonemptyEquidimensional X d → H X →ₗ[F] F)
    (indexedPushforward : ∀ {X Y : V} {d e : ℕ},
      IsNonemptyEquidimensional X d → IsNonemptyEquidimensional Y e →
        (X ⟶ Y) → H X →ₗ[F] H Y)
    (pushforward_adjoint : ∀ {X Y : V} {d e : ℕ}
      (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e)
      (f : X ⟶ Y) (b : H Y) (a : H X),
      integral hX (pullback f b * a) =
        integral hY (b * indexedPushforward hX hY f a))
    (poincare_separates : ∀ {X : V} {d : ℕ}
      (hX : IsNonemptyEquidimensional X d) (x y : H X),
      (∀ c : H X, integral hX (c * x) = integral hX (c * y)) → x = y)
    {X Y : V} {d e : ℕ} (hX : IsNonemptyEquidimensional X d)
    (hY : IsNonemptyEquidimensional Y e) (f : X ⟶ Y) (b : H Y) (a : H X) :
    indexedPushforward hX hY f (pullback f b * a) =
      b * indexedPushforward hX hY f a := sorry

/-- Pushforwards indexed by dimension witnesses are compatible with composition
when they are adjoint to a composition-compatible pullback and their indexed
trace pairings separate equality. -/
theorem pushforward_comp_of_indexedTrace
    (IsNonemptyEquidimensional : V → ℕ → Prop)
    (integral : ∀ {X : V} {d : ℕ},
      IsNonemptyEquidimensional X d → H X →ₗ[F] F)
    (indexedPushforward : ∀ {X Y : V} {d e : ℕ},
      IsNonemptyEquidimensional X d → IsNonemptyEquidimensional Y e →
        (X ⟶ Y) → H X →ₗ[F] H Y)
    (pullback_comp : ∀ {X Y Z : V} (f : X ⟶ Y) (g : Y ⟶ Z),
      pullback (f ≫ g) = (pullback f).comp (pullback g))
    (pushforward_adjoint : ∀ {X Y : V} {d e : ℕ}
      (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e)
      (f : X ⟶ Y) (b : H Y) (a : H X),
      integral hX (pullback f b * a) =
        integral hY (b * indexedPushforward hX hY f a))
    (poincare_separates : ∀ {X : V} {d : ℕ}
      (hX : IsNonemptyEquidimensional X d) (x y : H X),
      (∀ c : H X, integral hX (c * x) = integral hX (c * y)) → x = y)
    {X Y Z : V} {d e n : ℕ} (hX : IsNonemptyEquidimensional X d)
    (hY : IsNonemptyEquidimensional Y e) (hZ : IsNonemptyEquidimensional Z n)
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (indexedPushforward hY hZ g).comp (indexedPushforward hX hY f) =
      indexedPushforward hX hZ (f ≫ g) := sorry

/-- For a product equipped with a Künneth map and indexed trace pairing,
pushforward along the second projection sends a pure tensor to the second
factor scaled by the integral of the first. -/
theorem pushforward_snd_kunnethMap_tmul_of_indexedTrace
    {V : Type u} [Category.{v} V] {F : Type w} [Field F] [CharZero F]
    (H : V → Type x) [∀ Z, Ring (H Z)] [∀ Z, Algebra F (H Z)]
    (product : V → V → V) (fst : ∀ X Y, product X Y ⟶ X)
    (snd : ∀ X Y, product X Y ⟶ Y)
    (pullback : ∀ {X Y : V}, (X ⟶ Y) → H Y →ₐ[F] H X)
    (IsNonemptyEquidimensional : V → ℕ → Prop)
    (product_isNonemptyEquidimensional : ∀ {X Y : V} {d e : ℕ},
      IsNonemptyEquidimensional X d → IsNonemptyEquidimensional Y e →
        IsNonemptyEquidimensional (product X Y) (d + e))
    (indexedPushforward : ∀ {X Y : V} {d e : ℕ},
      IsNonemptyEquidimensional X d → IsNonemptyEquidimensional Y e →
        (X ⟶ Y) → H X →ₗ[F] H Y)
    (kunnethMap : ∀ X Y, H X ⊗[F] H Y →ₗ[F] H (product X Y))
    (integral : ∀ {X : V} {d : ℕ},
      IsNonemptyEquidimensional X d → H X →ₗ[F] F)
    (h_kunneth : ∀ X Y, Function.Bijective (kunnethMap X Y))
    (kunnethMap_tmul : ∀ {X Y : V} (a : H X) (b : H Y),
      kunnethMap X Y (a ⊗ₜ[F] b) =
        pullback (fst X Y) a * pullback (snd X Y) b)
    (integral_kunnethMap_tmul : ∀ {X Y : V} {d e : ℕ}
      (hX : IsNonemptyEquidimensional X d) (hY : IsNonemptyEquidimensional Y e)
      (a : H X) (b : H Y),
      integral (product_isNonemptyEquidimensional hX hY)
          (kunnethMap X Y (a ⊗ₜ[F] b)) = integral hX a * integral hY b)
    (pushforward_adjoint : ∀ {S T : V} {d e : ℕ}
      (hS : IsNonemptyEquidimensional S d) (hT : IsNonemptyEquidimensional T e)
      (f : S ⟶ T) (x : H S) (c : H T),
      integral hS (x * pullback f c) =
        integral hT (indexedPushforward hS hT f x * c))
    (poincare_separates : ∀ {X : V} {d : ℕ}
      (hX : IsNonemptyEquidimensional X d) (x y : H X),
      (∀ c : H X, integral hX (x * c) = integral hX (y * c)) → x = y)
    {X Y : V} {d e : ℕ} (hX : IsNonemptyEquidimensional X d)
    (hY : IsNonemptyEquidimensional Y e) (a : H X) (b : H Y) :
    indexedPushforward (product_isNonemptyEquidimensional hX hY) hY (snd X Y)
        (kunnethMap X Y (a ⊗ₜ[F] b)) = (integral hX a) • b := sorry

end WeilCohomology
