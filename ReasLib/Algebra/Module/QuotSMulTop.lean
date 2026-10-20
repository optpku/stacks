/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.QuotSMulTop
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Scalar towers for principal module quotients

Mathlib already owns the quotient module and its principal-torsion theorem.
This opt-in leaf supplies the compatible scalar tower, which is canonical for
the standard quotient `M / fM`.
-/

@[expose] public section

universe u v

namespace QuotSMulTop

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The canonical `R ⧸ (f)`-module structure on `M / fM` is compatible with its
original `R`-module structure. -/
@[stacks 0H7N "principal quotient scalar tower"]
instance instIsScalarTower (f : R) :
    IsScalarTower R (R ⧸ Ideal.span ({f} : Set R)) (QuotSMulTop f M) := sorry
/- Proof strategy: identify the quotient action with the canonical principal
torsion action using `Module.isTorsionBy_quotient_element_smul`, then apply the
quotient-module scalar tower construction. -/

end QuotSMulTop
