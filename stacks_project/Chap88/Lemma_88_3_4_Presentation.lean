/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent.BaseChange.Presentation

/-!
# Completed presentations under base change

The same-variable presentation of completed tensor base change is available to
consumers through its mathematical owner.
-/

universe u

open Algebra.NaiveCotangent.Adic
open Algebra.TopologicallyFiniteType

/- Lemma 88.3.4: Completed base change carries the induced finite completed
polynomial presentation. -/
#check (Algebra.NaiveCotangent.Adic.Presentation.baseChange :
    ∀ {A1 A2 : Type u} [CommRing A1] [CommRing A2] [Algebra A1 A2]
      {B1 : Type u} [CommRing B1] [Algebra A1 B1]
      (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ},
      1 ≤ c → I1.map (algebraMap A1 A2) ^ c ≤ I2 → I2.FG →
      ∀ [IsNoetherianRing A1] [IsNoetherianRing A2]
        [Algebra.TopologicallyFiniteType I1 B1] {ι : Type u} [Fintype ι],
        Presentation A1 B1 I1 ι →
          Presentation A2 (completedBaseChange A1 I2 B1) I2 ι)
