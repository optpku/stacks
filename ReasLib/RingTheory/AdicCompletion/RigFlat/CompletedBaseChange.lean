/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.RigFlat
public import ReasLib.Topology.Algebra.TensorProduct.CompletedRing

/-!
# Rig-flatness under completed base change

Completed tensor products over rig-flat structure maps are adic Noetherian,
and their canonical right inclusions are rig-flat under adic, topologically
finite-type base change.
-/

@[expose] public section

universe u

namespace Algebra.TensorProduct.Completed

/-- The completed tensor product of adic Noetherian algebras, formed over a
rig-flat left structure map and an adic right structure map, remains adic. -/
instance instIsAdicRing {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [TopologicalRing.IsAdicRing C]
    [IsNoetherianRing B] [IsNoetherianRing C]
    [RingHom.RigFlat (algebraMap A B)]
    [hC : Fact ((algebraMap A C).IsAdicHom)] :
    TopologicalRing.IsAdicRing (Completed A B C) :=
  sorry

/-- The completed tensor product of adic Noetherian algebras remains Noetherian
when the left structure map is rig-flat. -/
instance instIsNoetherianRing {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [TopologicalRing.IsAdicRing C]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    [RingHom.RigFlat (algebraMap A B)]
    [hC : Fact ((algebraMap A C).IsAdicHom)] :
    IsNoetherianRing (Completed A B C) :=
  sorry

end Algebra.TensorProduct.Completed

open Algebra.TensorProduct.Completed

namespace RingHom.RigFlat

/-- Completed base change of a rig-flat homomorphism along an adic,
topologically finite-type homomorphism of adic Noetherian rings is rig-flat
on the canonical right inclusion into the completed tensor product. -/
@[instance]
theorem completedBaseChange {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [TopologicalRing.IsAdicRing C]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsNoetherianRing C]
    [RigFlat (algebraMap A B)]
    [h_adic : Fact ((algebraMap A C).IsAdicHom)]
    [h_tft : Fact ((algebraMap A C).TopologicallyFiniteType)] :
    RigFlat (includeRight A B C) :=
  sorry


end RingHom.RigFlat
