/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Monoidal.Invertible
public import stacks_project.Chap71.Definition_71_10_9_Regular
public import stacks_project.Chap71.Lemma_71_10_8_Stalk

/-!
# Lemma 71.10.11

If an algebraic space `X` over a scheme `S` satisfies (a), (b), and (c) of
Lemma 71.10.8, then every invertible `𝒪_X`-module `L` has a regular meromorphic
section.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalCategory.isInvertibleObject

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 71.10.11: let `S` be a scheme and let `X` be an algebraic space over `S`
satisfying (a), (b), and (c) of Lemma 71.10.8. Then every invertible `𝒪_X`-module
`L` has a regular meromorphic section. -/
@[stacks 0EPQ]
theorem exists_isRegularMeromorphicSection {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X)
    (hmono : ∀ η ∈ codimZeroPoints X, existsMonoFieldValuedPoint X η)
    (L : X.Modules) [isInvertibleObject L] :
    ∃ s : meromorphicSections X L, IsRegularMeromorphicSection X L s :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
