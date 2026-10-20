module

public import ReasLib.RingTheory.AdicCompletion.RigSmooth
public import ReasLib.Algebra.Category.CommAlgCat.TopologicallyFiniteType.BaseChange
public import Mathlib.RingTheory.Spectrum.Prime.Basic

@[expose] public section

universe u

open Algebra.TopologicallyFiniteType
open PrimeSpectrum

namespace Algebra.RigSmooth

/-- Completed base change along a map of Noetherian rings preserves rig-smoothness
when the extension of the source ideal and the target ideal have the same zero locus. -/
@[stacks 0GAM]
theorem of_baseChange {A1 A2 B1 : Type u} [CommRing A1] [CommRing A2]
    [Algebra A1 A2] [CommRing B1] [Algebra A1 B1]
    [IsNoetherianRing A1] [IsNoetherianRing A2] (I1 : Ideal A1) (I2 : Ideal A2)
    [RigSmooth I1 B1]
    (hV : zeroLocus (I1.map (algebraMap A1 A2) : Set A2) =
      zeroLocus (I2 : Set A2)) :
    RigSmooth I2 (completedBaseChange A1 I2 B1) :=
  sorry

end Algebra.RigSmooth
