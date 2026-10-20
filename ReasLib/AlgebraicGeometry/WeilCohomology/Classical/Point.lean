/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Equiv
public import ReasLib.AlgebraicGeometry.WeilCohomology.Classical

@[expose] public section

noncomputable section

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

variable (T : ClassicalTheory k F V dimension product fst snd point H CH Hgrade CHgrade
  cyclePullback cyclePushforward (1 : CHgrade point 0))

include T

/-- Cohomology of the distinguished point vanishes in every nonzero degree. -/
theorem pointCohomology_isZero :
    ∀ i : ℤ, i ≠ 0 → Hgrade point i = ⊥ := sorry

/-- The cycle class of the canonical degree-zero cycle on the distinguished point is one. -/
theorem pointFundamentalCycleClass_eq_one :
    T.cycleClass point (1 : CHgrade point 0) = 1 := sorry

/-- Integration on the distinguished point sends one to one. -/
theorem pointIntegral_one :
    T.integral point 1 = 1 := sorry

/-- Integration on degree-zero cohomology of the distinguished point is a left inverse
to the scalar map. -/
theorem pointAlgebraMap_leftInverse_integral :
    Function.LeftInverse
      ((T.integral point).comp (Hgrade point 0).subtype)
      (algebraMap F (Hgrade point 0)) := sorry

/-- Integration on degree-zero cohomology of the distinguished point is a right inverse
to the scalar map. -/
theorem pointAlgebraMap_rightInverse_integral :
    Function.RightInverse
      ((T.integral point).comp (Hgrade point 0).subtype)
      (algebraMap F (Hgrade point 0)) := sorry

/-- The canonical algebra equivalence from the coefficient field to degree-zero
cohomology of the distinguished point, with scalar map forward and integration backward. -/
noncomputable def pointAlgEquiv : F ≃ₐ[F] Hgrade point 0 :=
  AlgEquiv.ofLinearEquiv
    (LinearEquiv.mk
      (Algebra.ofId F (Hgrade point 0)).toLinearMap
      ((T.integral point).comp (Hgrade point 0).subtype)
      (pointAlgebraMap_leftInverse_integral T)
      (pointAlgebraMap_rightInverse_integral T))
    (map_one (Algebra.ofId F (Hgrade point 0)))
    (map_mul (Algebra.ofId F (Hgrade point 0)))

/-- The canonical point equivalence sends a scalar to its image under the algebra map. -/
theorem pointAlgEquiv_apply (a : F) :
    pointAlgEquiv T a = algebraMap F (Hgrade point 0) a := sorry

/-- The inverse of the canonical point equivalence is integration restricted to degree zero. -/
theorem pointAlgEquiv_symm_apply (a : Hgrade point 0) :
    (pointAlgEquiv T).symm a = T.integral point a := sorry

/-- Every algebra equivalence from the coefficient field to degree-zero cohomology of
the distinguished point is the canonical point equivalence. -/
theorem pointAlgEquiv_unique (e : F ≃ₐ[F] Hgrade point 0) :
    e = pointAlgEquiv T := sorry

end WeilCohomology.ClassicalTheory
