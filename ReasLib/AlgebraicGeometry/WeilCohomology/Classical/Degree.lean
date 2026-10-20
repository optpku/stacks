/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.WeilCohomology.Classical

@[expose] public section

open CategoryTheory

universe u v w x y z

namespace WeilCohomology.ClassicalTheory

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {F : Type v} [Field F] [CharZero F]
variable {V : Type w} [Category.{z} V]
variable {dimension : V → ℕ} {product : V → V → V}
variable {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
variable {point : V} {H : V → Type x} {CH : V → Type y}
variable [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] [∀ X, CommRing (CH X)]
variable {Hgrade : ∀ X, ℤ → Submodule F (H X)}
variable {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)}
variable [∀ X, GradedAlgebra (Hgrade X)] [∀ X, GradedAlgebra (CHgrade X)]
variable {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
variable {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
variable {pointCycle : CHgrade point 0}

/-- For a top-codimension cycle in a classical Weil cohomology theory, the
integral of its cycle class is its integer degree viewed in the coefficient field. -/
theorem integral_cycleClass_eq_degree
    (T : ClassicalTheory k F V dimension product fst snd point H CH Hgrade CHgrade
      cyclePullback cyclePushforward pointCycle)
    (X : V) (toPoint : X ⟶ point)
    (degree : CHgrade X (dimension X : ℤ) →+ ℤ)
    (degree_spec : ∀ α : CHgrade X (dimension X : ℤ),
      cyclePushforward toPoint α = degree α • pointCycle)
    (α : CHgrade X (dimension X : ℤ)) :
    T.integral X (T.cycleClass X α) = (degree α : F) := sorry

end WeilCohomology.ClassicalTheory
