/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Field.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPowerSeries.Basic

@[expose] public section

noncomputable section

universe u

namespace MvPowerSeries

variable {k : Type u} [Field k]

/-- Over a field, a perturbation of `X 0 * X 1` in the cube of the coordinate ideal
is the image of `X 0 * X 1` under a power-series algebra automorphism. -/
theorem exists_algEquiv_map_X_mul_X (δ : MvPowerSeries (Fin 2) k)
    (hδ : δ ∈ (Ideal.span {X (0 : Fin 2), X (1 : Fin 2)}) ^ 3) :
    ∃ e : MvPowerSeries (Fin 2) k ≃ₐ[k] MvPowerSeries (Fin 2) k,
      e (X (0 : Fin 2) * X (1 : Fin 2)) = X (0 : Fin 2) * X (1 : Fin 2) + δ := sorry

/-- Over a field, the power-series quotients by `X 0 * X 1` and by its perturbation
in the cube of the coordinate ideal are isomorphic as algebras over the field. -/
theorem nodeQuotient_algEquiv (δ : MvPowerSeries (Fin 2) k)
    (hδ : δ ∈ (Ideal.span {X (0 : Fin 2), X (1 : Fin 2)}) ^ 3) :
    Nonempty
      ((MvPowerSeries (Fin 2) k ⧸
          Ideal.span {(X (0 : Fin 2) * X (1 : Fin 2) : MvPowerSeries (Fin 2) k)}) ≃ₐ[k]
        (MvPowerSeries (Fin 2) k ⧸
          Ideal.span {(X (0 : Fin 2) * X (1 : Fin 2) + δ : MvPowerSeries (Fin 2) k)})) := sorry

/-- Over a field, the power-series quotients by `X 0 * X 1` and by its perturbation
in the cube of the coordinate ideal are isomorphic as rings. -/
theorem nodeQuotient_ringEquiv (δ : MvPowerSeries (Fin 2) k)
    (hδ : δ ∈ (Ideal.span {X (0 : Fin 2), X (1 : Fin 2)}) ^ 3) :
    Nonempty
      ((MvPowerSeries (Fin 2) k ⧸
          Ideal.span {(X (0 : Fin 2) * X (1 : Fin 2) : MvPowerSeries (Fin 2) k)}) ≃+*
        (MvPowerSeries (Fin 2) k ⧸
          Ideal.span {(X (0 : Fin 2) * X (1 : Fin 2) + δ : MvPowerSeries (Fin 2) k)})) := sorry

end MvPowerSeries
