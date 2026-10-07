module

public import stacks_project.Chap71.Definition_71_10_9_Regular
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Definition 71.10.9
Let `S` be a scheme. Let `X` be an algebraic space over `S`. Let `ℒ` be an invertible
`𝒪_X`-module. A meromorphic section `s` of `ℒ` is said to be regular if the induced map
`𝒦_X ⟶ 𝒦_X(ℒ)` is injective. The checked predicate is the canonical generalization to an
arbitrary module sheaf. -/
@[stacks 0ENB] #check
  (IsRegularMeromorphicSection :
    {S : Scheme.{u}} → (X : AlgebraicSpace S) →
      (F : X.Modules) → meromorphicSections X F → Prop)
