/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import stacks_project.Chap88.Definition_88_18_1_Ring
public import stacks_project.Chap88.«88_2_3_2_BaseChange»

/-!
# Base change of rig-smooth algebras

A map of Noetherian rings `A1 → A2` with `V(I1 A2) = V(I2)` preserves
rig-smoothness of a C' algebra under Remark 88.2.3 completed base change.
-/

@[expose] public section

universe u

open Algebra.TopologicallyFiniteType
open PrimeSpectrum

namespace Algebra.RigSmooth

/-- Lemma 88.4.5. Let `A1 → A2` be a map of Noetherian rings. Let `I1 ⊆ A1`
and `I2 ⊆ A2` be ideals such that `V(I1 A2) = V(I2)`. Let `B1` be in C'
(88.2.0.2) for `(A1, I1)`, and let `B2` be the completed base change of `B1`
as in Remark 88.2.3. If `B1` is rig-smooth over `(A1, I1)`, then `B2` is
rig-smooth over `(A2, I2)`. -/
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
