/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent.ExtAnnihilation
import StacksCheckRecall

/-!
# Ext¹ annihilation of completed naive cotangent objects after base change

A Remark 88.2.3 map of Noetherian pairs transports Ext¹ annihilation by `f1`
on `NL_{B1/A1}^∧` to Ext¹ annihilation by its image in the completed base
change.
-/

@[expose] public section

universe u

open CategoryTheory
open Algebra.NaiveCotangent.Adic
open Algebra.TopologicallyFiniteType
open CommAlgCat.TopologicallyFiniteType (includeLeftToCompletion)

/- Lemma 88.4.4: Let `(A1, I1) → (A2, I2)` be as in Remark 88.2.3 with `A1`
and `A2` Noetherian. Let `B1` be in (88.2.0.2) for `(A1, I1)`, and let `B2`
be the completed base change `(B1 ⊗[A1] A2)^∧`. If `f1 ∈ B1` annihilates
`Ext¹_{B1}(NL_{B1/A1}^∧, N1)` for every `B1`-module `N1`, then the image
`includeLeftToCompletion I2 B1 f1 ∈ B2` annihilates
`Ext¹_{B2}(NL_{B2/A2}^∧, N2)` for every `B2`-module `N2`. -/
@[stacks 0GAL] #check
  (Algebra.NaiveCotangent.Adic.twoTermExtOneAnnihilatedByIdeal_of_baseChange :
    ∀ {A1 A2 B1 ι : Type u}
      [CommRing A1] [CommRing A2] [Algebra A1 A2] [CommRing B1] [Algebra A1 B1]
      [IsNoetherianRing A1] [IsNoetherianRing A2]
      (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
      (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2)
      [Algebra.TopologicallyFiniteType I1 B1] [Fintype ι]
      (P : Presentation A1 B1 I1 ι) (f1 : B1),
    twoTermExtOneAnnihilatedByIdeal (naiveCotangentObject I1 P) (Ideal.span {f1}) →
    twoTermExtOneAnnihilatedByIdeal
      (naiveCotangentObject I2
        (Presentation.baseChange I1 I2 hc hI I2.fg_of_isNoetherianRing P))
      (Ideal.span {includeLeftToCompletion I2 B1 f1}))
