/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.TwoTerm.ExtAnnihilation
public import Mathlib.RingTheory.Noetherian.Defs
public import stacks_project.Chap88.Definition_88_8_1_Derived
public import stacks_project.Chap88.Lemma_88_3_4_Presentation

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

namespace Algebra.NaiveCotangent.Adic

variable {A1 A2 B1 ι : Type u}
variable [CommRing A1] [CommRing A2] [Algebra A1 A2] [CommRing B1] [Algebra A1 B1]
variable [IsNoetherianRing A1] [IsNoetherianRing A2]
variable (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
variable (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
variable [Algebra.TopologicallyFiniteType I1 B1]
variable [Fintype ι]
variable (P : Presentation A1 B1 I1 ι)

/-- Lemma 88.4.4: Let `(A1, I1) → (A2, I2)` be as in Remark 88.2.3 with `A1`
and `A2` Noetherian. Let `B1` be in (88.2.0.2) for `(A1, I1)`, and let `B2`
be the completed base change `(B1 ⊗[A1] A2)^∧`. If `f1 ∈ B1` annihilates
`Ext¹_{B1}(NL_{B1/A1}^∧, N1)` for every `B1`-module `N1`, then the image
`includeLeftToCompletion I2 B1 f1 ∈ B2` annihilates
`Ext¹_{B2}(NL_{B2/A2}^∧, N2)` for every `B2`-module `N2`. -/
@[stacks 0GAL]
theorem twoTermExtOneAnnihilatedByIdeal_of_baseChange (f1 : B1)
    (hf : twoTermExtOneAnnihilatedByIdeal (naiveCotangentObject I1 P) (Ideal.span {f1})) :
    twoTermExtOneAnnihilatedByIdeal
      (naiveCotangentObject I2 (Presentation.baseChange I1 I2 hc hI hI2 P))
      (Ideal.span {includeLeftToCompletion I2 B1 f1}) := sorry

end Algebra.NaiveCotangent.Adic
