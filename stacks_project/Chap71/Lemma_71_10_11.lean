module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.Existence

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

/- Lemma 71.10.11. Let `S` be a scheme and let `X` be an algebraic space over `S`
satisfying (a), (b), and (c) of Lemma 71.10.8. Then every invertible `𝒪_X`-module
`L` has a regular meromorphic section. -/
@[stacks 0EPQ] #check (AlgebraicGeometry.AlgebraicSpace.exists_isRegularMeromorphicSection :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X]
    (hweak : X.weakAss ⊆ codimZeroPoints X)
    (hmono : ∀ η ∈ codimZeroPoints X, existsMonoFieldValuedPoint X η)
    (L : X.Modules) [isInvertibleObject L],
    ∃ s : meromorphicSections X L, IsRegularMeromorphicSection X L s)
