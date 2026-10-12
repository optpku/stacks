/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap67.Lemma_67_48_6_Reduced
public import stacks_project.Chap67.Lemma_67_49_1_FiniteComponents
public import stacks_project.Chap71.Lemma_71_6_11_WeaklyAssociated

/-!
# Lemma 71.2.12

The weakly associated points of a reduced algebraic space are exactly its
codimension-`0` points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 71.2.12: for a scheme `S` and a reduced algebraic space `X` over `S`,
the weakly associated points of `X` are exactly the codimension `0` points of
`X`. -/
@[stacks 0EN1]
theorem weakAss_eq_codimZeroPoints {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsReduced X] : X.weakAss = codimZeroPoints X :=
  sorry

/-- Membership in `X.weakAss` is equivalent to membership in `codimZeroPoints X`
when `X` is reduced. -/
theorem mem_weakAss_iff_mem_codimZeroPoints {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsReduced X] (x : Points X) :
    x ∈ X.weakAss ↔ x ∈ codimZeroPoints X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
