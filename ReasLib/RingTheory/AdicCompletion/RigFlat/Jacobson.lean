/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.RigFlat
public import ReasLib.RingTheory.Topology.Adic.Jacobson

/-!
# Rig-flatness with Jacobson special fiber

For homomorphisms of adic Noetherian topological rings with Jacobson special
fiber in the source, naive rig-flatness and rig-flatness are equivalent.
-/

@[expose] public section

universe u

namespace RingHom.RigFlat

/-- A naively rig-flat homomorphism of adic Noetherian topological rings is
rig-flat if the quotient of its source by an ideal of definition is Jacobson. -/
@[stacks 0GGQ]
theorem of_naive {A B : Type u}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) [NaiveRigFlat φ] (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    [IsJacobsonRing (A ⧸ I)] :
    RigFlat φ :=
  sorry

/-- Under the Jacobson special-fiber hypothesis, a homomorphism of adic
Noetherian topological rings is rig-flat if and only if it is naively
rig-flat. -/
theorem iff_naive {A B : Type u}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) (I : Ideal A)
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I)
    [IsJacobsonRing (A ⧸ I)] :
    RigFlat φ ↔ NaiveRigFlat φ :=
  sorry

end RingHom.RigFlat
