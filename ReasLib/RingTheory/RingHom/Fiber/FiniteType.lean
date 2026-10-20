/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.FiniteType
import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.RingHom.Fiber.Basic

@[expose] public section

/-!
# Finite-type residue-field fibers

This leaf owns finiteness consequences for residue-field fibers of finite-type
algebras.
-/

universe u v

namespace Ideal.Fiber

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FiniteType R S]

/-- A residue-field fiber of a finite-type algebra is Noetherian. -/
@[stacks 00RH "Noetherian residue-field fiber of a finite-type algebra"]
noncomputable instance isNoetherianRing_of_finiteType
    (p : Ideal R) [p.IsPrime] : IsNoetherianRing (p.Fiber S) :=
  Algebra.FiniteType.isNoetherianRing p.ResidueField _

end Ideal.Fiber

namespace RingHom.FibersKrullDimLE

/-- For a finite-type homomorphism of commutative rings, a uniform bound on the
Krull dimensions of the fibers of evaluation at `a` also bounds the fibers of
evaluation at `a ^ n + b` for every sufficiently large `n`. -/
@[stacks 0GTF "eventual fiber-dimension bound after a power perturbation"]
theorem eventually_eval₂_pow_add
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) (h_finiteType : φ.FiniteType) (d : ℕ) (a b : S)
    (ha : RingHom.FibersKrullDimLE d (Polynomial.eval₂RingHom φ a)) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      RingHom.FibersKrullDimLE d (Polynomial.eval₂RingHom φ (a ^ n + b)) := sorry

end RingHom.FibersKrullDimLE
