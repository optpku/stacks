/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.Isomorphisms
public import ReasLib.Algebra.Module.IdealPower.Quotient
import Mathlib.Tactic.CrossRefAttribute

/-!
# Isomorphism systems over ideal-power quotients

This file first records the kernel API for consecutive positive ideal-power quotient stages.
It then owns the inverse system of linear equivalences between two such quotient systems.  The
reduction operation is concrete: it transports an equivalence through the quotients by the
transition kernels and the first isomorphism theorem.
@stack 09BB
-/

@[expose] public section

open CategoryTheory
open Opposite
open TypeCat

noncomputable section

universe u v w x

namespace Ideal.PowerQuotient

variable {R : Type u} [CommRing R]

/-- The kernel of the transition from exponent `n + 2` to exponent `n + 1`. -/
@[stacks 09BB "kernel of a positive ideal-power quotient transition"]
abbrev transitionKer
    (I : Ideal R) (M : ModuleCat.{v} R) (n : ℕ) :
    Submodule R (positiveStage I M (n + 1)) :=
  LinearMap.ker (positiveStep I M n).hom

/-- Every transition between consecutive positive ideal-power quotient stages is surjective. -/
@[stacks 09BB "surjectivity of a positive ideal-power quotient transition"]
theorem transition_surjective
    (I : Ideal R) (M : ModuleCat.{v} R) (n : ℕ) :
    Function.Surjective (positiveStep I M n).hom := sorry

/-- The transition kernel is the `I ^ (n + 1)`-multiple submodule of the higher stage. -/
@[stacks 09BB "kernel formula for a positive ideal-power quotient transition"]
theorem transitionKer_eq_pow_smulTop
    (I : Ideal R) (M : ModuleCat.{v} R) (n : ℕ) :
    transitionKer I M n =
      I ^ (n + 1) • (⊤ : Submodule R (positiveStage I M (n + 1))) := sorry

/-- A linear equivalence of higher quotient stages carries one transition kernel to the other. -/
@[stacks 09BB "transport of positive ideal-power transition kernels"]
theorem transitionKer_map_eq
    (I : Ideal R) (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    (n : ℕ)
    (e : positiveStage I M (n + 1) ≃ₗ[R] positiveStage I N (n + 1)) :
    (transitionKer I M n).map e.toLinearMap = transitionKer I N n := sorry

namespace Iso

/-- The type of linear equivalences between the `n`th positive ideal-power quotient stages. -/
@[stacks 09BB "linear equivalences between positive ideal-power quotient stages"]
abbrev stage
    (I : Ideal R) (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) (n : ℕ) :
    Type (max v w) :=
  positiveStage I M n ≃ₗ[R] positiveStage I N n

/-- Reduce an equivalence modulo `I ^ (n + 2)` to one modulo `I ^ (n + 1)`. -/
@[stacks 09BB "reduction of an ideal-power quotient equivalence"]
noncomputable def reduce
    (I : Ideal R) (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) (n : ℕ) :
    stage I M N (n + 1) → stage I M N n :=
  fun e ↦
    ((positiveStep I M n).hom.quotKerEquivOfSurjective
        (transition_surjective I M n)).symm.trans
      ((Submodule.Quotient.equiv
          (transitionKer I M n)
          (transitionKer I N n)
          e
          (transitionKer_map_eq I M N n e)).trans
        ((positiveStep I N n).hom.quotKerEquivOfSurjective
          (transition_surjective I N n)))

/-- The reduced equivalence makes the square with the two quotient transitions commute. -/
@[stacks 09BB "commutative square for reduction of quotient equivalences"]
theorem reduce_comp_step
    (I : Ideal R) (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    (n : ℕ) (e : stage I M N (n + 1)) :
    (reduce I M N n e).toLinearMap.comp (positiveStep I M n).hom =
      (positiveStep I N n).hom.comp e.toLinearMap := sorry

/-- Pointwise, reducing an equivalence commutes with reducing its argument. -/
@[simp, stacks 09BB "application of a reduced quotient equivalence"]
theorem reduce_apply
    (I : Ideal R) (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    (n : ℕ) (e : stage I M N (n + 1)) (m : positiveStage I M (n + 1)) :
    reduce I M N n e ((positiveStep I M n).hom m) =
      (positiveStep I N n).hom (e m) := sorry

/-- Reducing the identity equivalence gives the identity equivalence. -/
@[simp, stacks 09BB "reduction preserves identity quotient equivalences"]
theorem reduce_refl
    (I : Ideal R) (M : ModuleCat.{v} R) (n : ℕ) :
    reduce I M M n (LinearEquiv.refl R (positiveStage I M (n + 1))) =
      LinearEquiv.refl R (positiveStage I M n) := sorry

/-- Reduction preserves composition of quotient-stage equivalences. -/
@[stacks 09BB "reduction preserves composition of quotient equivalences"]
theorem reduce_trans
    (I : Ideal R)
    (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) (P : ModuleCat.{x} R)
    (n : ℕ) (e : stage I M N (n + 1)) (f : stage I N P (n + 1)) :
    reduce I M P n (e.trans f) =
      (reduce I M N n e).trans (reduce I N P n f) := sorry

/-- Reduction commutes with taking the inverse of a quotient-stage equivalence. -/
@[simp, stacks 09BB "reduction preserves inverse quotient equivalences"]
theorem reduce_symm
    (I : Ideal R) (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    (n : ℕ) (e : stage I M N (n + 1)) :
    (reduce I M N n e).symm = reduce I N M n e.symm := sorry

/-- The sequential inverse system of linear equivalences between positive quotient stages. -/
@[stacks 09BB "inverse system of positive ideal-power quotient equivalences"]
abbrev system
    (I : Ideal R) (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) :
    SequentialInverseSystem (Type (max v w)) :=
  @Functor.ofOpSequence (Type (max v w)) _
    (fun n ↦ stage I M N n)
    (fun n ↦ TypeCat.ofHom (reduce I M N n))

/-- The object at index `n` in the equivalence system is the explicit stage type. -/
@[simp, stacks 09BB "object of the ideal-power quotient equivalence system"]
theorem system_obj
    (I : Ideal R) (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) (n : ℕ) :
    (system I M N).obj (op n) = stage I M N n := sorry

/-- The successor map of the equivalence system is reduction by one quotient stage. -/
@[simp, stacks 09BB "successor map of the ideal-power quotient equivalence system"]
theorem system_stepMap
    (I : Ideal R) (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) (n : ℕ) :
    (system I M N).stepMap n = TypeCat.ofHom (reduce I M N n) := sorry

end Iso
end Ideal.PowerQuotient
