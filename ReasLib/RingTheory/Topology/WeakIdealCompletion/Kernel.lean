/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.WeakIdealCompletion
public import Mathlib.Topology.Algebra.Ring.Ideal

/-!
# Kernels of weak-ideal completion projections

Stage projections of weak-ideal completions are surjective. Over a weakly admissible
base, their kernels are closures of extended ideals and are open weak ideals of definition.
-/

@[expose] public section

noncomputable section

universe u

namespace TopologicalRing.weakIdealCompletion

variable {B A : Type u} [CommRing B] [TopologicalSpace B] [CommRing A] [Algebra B A]

/-- The stage projection from the weak-ideal completion onto a quotient is surjective. -/
theorem eval_surjective {J : Ideal B} (hJ : Ideal.IsWeakIdealOfDefinition J) :
    Function.Surjective (eval B A hJ) :=
  sorry

variable [IsWeaklyAdmissibleRing B]

/-- The kernel of a stage projection is the closure of the base ideal extended to
the weak-ideal completion. -/
theorem eval_ker_eq_closure {J : Ideal B} (hJ : Ideal.IsWeakIdealOfDefinition J) :
    RingHom.ker (eval B A hJ) =
      (J.map (algebraMap B (weakIdealCompletion B A))).closure :=
  sorry

/-- An element lies in a stage kernel if and only if it lies in the closure of the
extended base ideal. -/
theorem mem_eval_ker {J : Ideal B} (hJ : Ideal.IsWeakIdealOfDefinition J)
    {x : weakIdealCompletion B A} :
    x ∈ RingHom.ker (eval B A hJ) ↔
      x ∈ (J.map (algebraMap B (weakIdealCompletion B A))).closure :=
  sorry

/-- The kernel of a stage projection is a weak ideal of definition of the completion. -/
theorem isWeakIdealOfDefinition_eval_ker {J : Ideal B}
    (hJ : Ideal.IsWeakIdealOfDefinition J) :
    Ideal.IsWeakIdealOfDefinition (RingHom.ker (eval B A hJ)) :=
  sorry

/-- The kernel of each stage projection of the weak-ideal completion is open. -/
theorem isOpen_eval_ker {J : Ideal B} (hJ : Ideal.IsWeakIdealOfDefinition J) :
    IsOpen (RingHom.ker (eval B A hJ) : Set (weakIdealCompletion B A)) :=
  sorry

end TopologicalRing.weakIdealCompletion
