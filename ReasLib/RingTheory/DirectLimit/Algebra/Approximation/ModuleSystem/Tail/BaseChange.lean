/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.ModuleSystem.BaseChange
public import ReasLib.RingTheory.DirectLimit.Algebra.Approximation.ModuleSystem.Tail
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Base-change computations for module-system tails

This leaf records that the canonical module base-change maps of a generic
directed module system are unchanged after restriction to a cofinal tail.
It is independent of finite-type and finite-module specialization data.
-/

@[expose] public section

open scoped TensorProduct

universe u v x y

noncomputable section

namespace Ring.DirectLimit.Algebra.Approximation.ModuleSystem

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {f : R →+* S} {M : Type x} [AddCommGroup M] [_root_.Module S M]

/-- A module-system tail has the original transition base-change map at every
pair of comparable tail stages. -/
@[simp, stacks 00R1 "directed module-system tail"]
theorem tail_transitionBaseChangeMap (A : ModuleSystem f M) (i₀ : A.index)
    {j k : Set.Ici i₀} (h : j ≤ k) :
    (A.tail i₀).transitionBaseChangeMap h = A.transitionBaseChangeMap h := sorry

/-- A module-system tail has the original final base-change computation at
every tail stage. -/
@[simp, stacks 00R1 "directed module-system tail"]
theorem tail_finalBaseChangeMap_tmul (A : ModuleSystem f M) (i₀ : A.index)
    (j : Set.Ici i₀) (s : S) (m : A.moduleStage j.1) :
    let _ : Algebra ((A.tail i₀).target j) S :=
      ((A.tail i₀).toHom.targetToLimit j).toAlgebra
    (A.tail i₀).finalBaseChangeMap j
        (s ⊗ₜ[(A.tail i₀).target j] m) =
      s • A.moduleToLimit j.1 m := sorry

end Ring.DirectLimit.Algebra.Approximation.ModuleSystem
