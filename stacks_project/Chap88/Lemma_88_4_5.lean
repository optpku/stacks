/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.RigSmooth.BaseChange
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 88.4.5. Let `A1 → A2` be a map of Noetherian rings. Let `I1 ⊆ A1`
and `I2 ⊆ A2` be ideals such that `V(I1 A2) = V(I2)`. Let `B1` be in C'
(88.2.0.2) for `(A1, I1)`, and let `B2` be the completed base change of `B1`
as in Remark 88.2.3. If `B1` is rig-smooth over `(A1, I1)`, then `B2` is
rig-smooth over `(A2, I2)`. -/
@[stacks 0GAM] #check (Algebra.RigSmooth.of_baseChange :
  ∀ {A1 A2 B1 : Type u} [CommRing A1] [CommRing A2]
    [Algebra A1 A2] [CommRing B1] [Algebra A1 B1]
    [IsNoetherianRing A1] [IsNoetherianRing A2] (I1 : Ideal A1) (I2 : Ideal A2)
    [Algebra.RigSmooth I1 B1],
    PrimeSpectrum.zeroLocus (I1.map (algebraMap A1 A2) : Set A2) =
      PrimeSpectrum.zeroLocus (I2 : Set A2) →
    Algebra.RigSmooth I2 (Algebra.TopologicallyFiniteType.completedBaseChange A1 I2 B1))
