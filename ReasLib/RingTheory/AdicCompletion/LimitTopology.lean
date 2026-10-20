/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.UniformSpace.Pi

@[expose] public section

noncomputable section

universe u

namespace AdicCompletion

/-- The adic completion equipped with the inverse-limit topology of discrete quotients. -/
def WithLimitTopology {A : Type u} [CommRing A] (I : Ideal A) : Type u :=
  AdicCompletion I A

namespace WithLimitTopology

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- The inverse-limit completion inherits its ring operations from the adic completion. -/
instance instCommRing : CommRing (WithLimitTopology I) :=
  inferInstanceAs (CommRing (AdicCompletion I A))

/-- The inverse-limit completion is an algebra via the canonical completion map. -/
instance instAlgebra : Algebra A (WithLimitTopology I) :=
  inferInstanceAs (Algebra A (AdicCompletion I A))

/-- The topology is induced by the compatible family in the product of discrete quotients. -/
instance instTopologicalSpace : TopologicalSpace (WithLimitTopology I) :=
  TopologicalSpace.induced (fun (family : WithLimitTopology I) ↦ family.val)
    (@Pi.topologicalSpace ℕ (fun n ↦ A ⧸ (I ^ n • ⊤ : Submodule A A))
      (fun _ ↦ ⊥))

/-- For a finitely generated ideal, the inverse-limit topology is adic for its extension. -/
theorem isAdic_of_fg (hI : I.FG) :
    IsAdic (I.map (algebraMap A (WithLimitTopology I))) := sorry

end WithLimitTopology

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- The inverse-limit uniformity is comapped from the product of discrete quotient stages. -/
@[implicit_reducible]
def limitUniformSpace : UniformSpace (AdicCompletion I A) :=
  UniformSpace.comap (AdicCompletion.incl I A)
    (@Pi.uniformSpace ℕ (fun n ↦ A ⧸ (I ^ n • ⊤ : Submodule A A)) (fun _ ↦ ⊥))

/-- The topology of the inverse-limit uniformity is the induced discrete-stage topology. -/
theorem limitUniformSpace_topology :
    (limitUniformSpace I).toTopologicalSpace = WithLimitTopology.instTopologicalSpace I := sorry

/-- Every adic completion is complete for its discrete-stage inverse-limit uniformity. -/
instance completeSpace_limitUniformSpace :
    @CompleteSpace (AdicCompletion I A) (limitUniformSpace I) := sorry

end AdicCompletion
