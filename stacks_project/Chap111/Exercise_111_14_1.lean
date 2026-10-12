/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.MvPowerSeries.SplitNode
import StacksCheckRecall

@[expose] public section

universe u

open MvPowerSeries

/- Exercise 111.14.1: over any field, a cubic perturbation of the split node
defines an isomorphic power-series quotient ring. -/
@[stacks 02DM] #check (MvPowerSeries.nodeQuotient_ringEquiv :
  ∀ {k : Type u} [Field k] (δ : MvPowerSeries (Fin 2) k),
    δ ∈ (Ideal.span {X (0 : Fin 2), X (1 : Fin 2)}) ^ 3 →
    Nonempty
      ((MvPowerSeries (Fin 2) k ⧸
          Ideal.span {(X (0 : Fin 2) * X (1 : Fin 2) : MvPowerSeries (Fin 2) k)}) ≃+*
        (MvPowerSeries (Fin 2) k ⧸
          Ideal.span {(X (0 : Fin 2) * X (1 : Fin 2) + δ : MvPowerSeries (Fin 2) k)})))

/- The quotient rings are also isomorphic as algebras over the coefficient field. -/
#check (MvPowerSeries.nodeQuotient_algEquiv :
  ∀ {k : Type u} [Field k] (δ : MvPowerSeries (Fin 2) k),
    δ ∈ (Ideal.span {X (0 : Fin 2), X (1 : Fin 2)}) ^ 3 →
    Nonempty
      ((MvPowerSeries (Fin 2) k ⧸
          Ideal.span {(X (0 : Fin 2) * X (1 : Fin 2) : MvPowerSeries (Fin 2) k)}) ≃ₐ[k]
        (MvPowerSeries (Fin 2) k ⧸
          Ideal.span {(X (0 : Fin 2) * X (1 : Fin 2) + δ : MvPowerSeries (Fin 2) k)})))

/- A power-series algebra automorphism realizes the perturbation exactly. -/
#check (MvPowerSeries.exists_algEquiv_map_X_mul_X :
  ∀ {k : Type u} [Field k] (δ : MvPowerSeries (Fin 2) k),
    δ ∈ (Ideal.span {X (0 : Fin 2), X (1 : Fin 2)}) ^ 3 →
    ∃ e : MvPowerSeries (Fin 2) k ≃ₐ[k] MvPowerSeries (Fin 2) k,
      e (X (0 : Fin 2) * X (1 : Fin 2)) = X (0 : Fin 2) * X (1 : Fin 2) + δ)
