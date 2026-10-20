/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.RigEtale
public import ReasLib.RingTheory.Topology.Noetherian.Cancellation

/-!
# Cancellation for rig-étale homomorphisms of Noetherian adic rings
-/

@[expose] public section

universe u

open RingHom

namespace TopologicalRing.Noetherian

/-- Rig-étaleness has the cancellation property for continuous homomorphisms
of commutative Noetherian adic topological rings: if `ψ` and `φ.comp ψ` are
rig-étale, then `φ` is rig-étale. -/
theorem hasCancellationProperty_rigEtale :
    HasCancellationProperty
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
        (φ : B →+* A) ↦ φ.RigEtale :=
  sorry

end TopologicalRing.Noetherian
