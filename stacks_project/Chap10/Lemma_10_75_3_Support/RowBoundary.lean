/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap10.Lemma_10_75_3_Support.Core
import StacksCheckRecall

@[expose] public section

/-!
Row-boundary support for Lemma 10.75.3.
@stack 00M1
-/

open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂ ComplexShape

noncomputable section

universe u

section

variable {R : Type u} [Ring R]

/-- Lemma 10.75.3 support: if the rows of `A` resolve `R(A)_•`, then the canonical map from
`Tot(A)` to `R(A)_•` is a quasi-isomorphism. -/
@[stacks 00M1 "row comparison quasi-isomorphism"]
theorem totalToRowCokernel_quasiIso
    (A : HomologicalComplex₂ (ModuleCat R) (down ℕ) (down ℕ))
    (hrows : RowsResolve A) :
    QuasiIso (totalToRowCokernel A) := sorry

@[stacks 00M1 "row comparison quasi-isomorphism"]
#check @totalToRowCokernel_quasiIso

end
