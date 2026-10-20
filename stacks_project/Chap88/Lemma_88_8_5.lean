/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent.BaseChange.ScalarAnnihilation
import StacksCheckRecall

/-!
# Vanishing of scalars on completed naive cotangent objects after base change

A Remark 88.2.3 map of Noetherian pairs transports vanishing of multiplication
by `f1` on `NL_{B1/A1}^∧` in `D(B1)` to vanishing of multiplication by its
image in the completed base change.
-/

@[expose] public section

universe u

open CategoryTheory
open Algebra.NaiveCotangent.Adic
open Algebra.TopologicallyFiniteType
open CommAlgCat.TopologicallyFiniteType (includeLeftToCompletion)

/- Lemma 88.8.5: Let `(A1, I1) → (A2, I2)` be as in Remark 88.2.3 with `A1`
and `A2` Noetherian. Let `B1` be in (88.2.0.2) for `(A1, I1)`, and let `B2`
be the completed base change `(B1 ⊗[A1] A2)^∧`. If multiplication by
`f1 ∈ B1` on `NL_{B1/A1}^∧` is zero in `D(B1)`, then multiplication by the
image `includeLeftToCompletion I2 B1 f1 ∈ B2` on `NL_{B2/A2}^∧` is zero in
`D(B2)`. -/
@[stacks 0AK2] #check
  (Algebra.NaiveCotangent.Adic.smul_id_naiveCotangentObject_eq_zero_of_baseChange :
    ∀ {A1 A2 B1 ι : Type u}
      [CommRing A1] [CommRing A2] [Algebra A1 A2] [CommRing B1] [Algebra A1 B1]
      [IsNoetherianRing A1] [IsNoetherianRing A2]
      (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
      (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
      [Algebra.TopologicallyFiniteType I1 B1] [Fintype ι]
      (P : Presentation A1 B1 I1 ι) (f1 : B1),
      f1 • 𝟙 (naiveCotangentObject I1 P) = 0 →
        (includeLeftToCompletion I2 B1 f1 : completedBaseChange A1 I2 B1) •
          𝟙 (naiveCotangentObject I2 (Presentation.baseChange I1 I2 hc hI hI2 P)) = 0)
