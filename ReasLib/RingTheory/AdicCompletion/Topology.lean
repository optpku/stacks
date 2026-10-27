/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.LimitTopology
public import ReasLib.RingTheory.Topology.Adic.Complete
public import ReasLib.RingTheory.Topology.WeaklyAdmissible
public import ReasLib.RingTheory.Topology.Adic.Weakly

@[expose] public section

noncomputable section

universe u

namespace AdicCompletion

namespace WithLimitTopology

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- The inverse-limit completion is a complete separated weakly admissible ring. -/
instance instIsWeaklyAdmissibleRing :
    TopologicalRing.IsWeaklyAdmissibleRing (WithLimitTopology I) := sorry

/-- The inverse-limit completion of a finitely generated ideal is an adic ring. -/
theorem isAdicRing_of_fg (hI : I.FG) :
    TopologicalRing.IsAdicRing (WithLimitTopology I) := sorry

/-- The inverse-limit completion is weakly adic for every ideal. -/
instance instIsWeaklyAdicRing :
    TopologicalRing.IsWeaklyAdicRing (WithLimitTopology I) := sorry

/-- The kernel of evaluation at the quotient by the `(n + 1)`st power. -/
def evalKernel (n : ℕ) : Ideal (WithLimitTopology I) :=
  RingHom.ker (AdicCompletion.evalₐ I (n + 1)).toRingHom

/-- Evaluation kernels are weak ideals of definition in the inverse-limit topology. -/
theorem evalKernel_isWeakIdealOfDefinition (n : ℕ) :
    TopologicalRing.Ideal.IsWeakIdealOfDefinition (evalKernel I n) := sorry

end WithLimitTopology

end AdicCompletion
