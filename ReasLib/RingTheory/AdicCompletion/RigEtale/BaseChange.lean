/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.RigEtale
public import ReasLib.Algebra.Category.CommAlgCat.TopologicallyFiniteType.BaseChange
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import ReasLib.RingTheory.Topology.Noetherian.BaseChange

@[expose] public section

universe u

open Algebra.TopologicallyFiniteType

namespace Algebra.RigEtale

/-- Completed base change along a map of Noetherian rings preserves rig-étaleness
when the extension of the source ideal and the target ideal have the same zero locus. -/
@[stacks 0GB2]
theorem of_baseChange {A1 A2 : Type u} [CommRing A1] [CommRing A2]
    [Algebra A1 A2] [IsNoetherianRing A1] [IsNoetherianRing A2]
    (I1 : Ideal A1) (I2 : Ideal A2)
    (hV : PrimeSpectrum.zeroLocus (I1.map (algebraMap A1 A2) : Set A2) =
      PrimeSpectrum.zeroLocus (I2 : Set A2))
    {B1 : Type u} [CommRing B1] [Algebra A1 B1] [RigEtale I1 B1] :
    RigEtale I2 (completedBaseChange A1 I2 B1) :=
  sorry

end Algebra.RigEtale

namespace TopologicalRing.Noetherian

/-- Rig-étale homomorphisms of Noetherian adic rings are stable under completed
base change by adic homomorphisms: the completed tensor product is adic
Noetherian and its canonical map from the base-changed ring is rig-étale. -/
@[stacks 0GCW]
theorem isStableUnderBaseChangeBy_rigEtale_isAdicHom :
    IsLocalMorphismProperty.IsStableUnderBaseChangeBy
      (fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
        (φ : B →+* A) ↦ φ.RigEtale)
      (fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
        (φ : B →+* A) ↦ φ.IsAdicHom) :=
  sorry

end TopologicalRing.Noetherian
