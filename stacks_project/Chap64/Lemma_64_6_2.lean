/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.CategoryTheory.DerivedCategory.Bounded
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe w v u

/- Lemma 64.6.2. An object `E` of `D(𝒜)` is contained in `D⁺(𝒜)` if and only if
`H⁽i⁾(E) = 0` for all `i ≪ 0`. Similar statements hold for `D⁻(𝒜)` and `Dᵇ(𝒜)`. -/
@[stacks 03T5] #check (@CategoryTheory.DerivedCategory.plus_iff :
  ∀ {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]
    (K : DerivedCategory 𝒜),
    (DerivedCategory.TStructure.t.plus : ObjectProperty (DerivedCategory 𝒜)) K ↔
      ∃ n : ℤ, ∀ i < n, Limits.IsZero ((DerivedCategory.homologyFunctor 𝒜 i).obj K))
@[stacks 03T5] #check (@CategoryTheory.DerivedCategory.minus_iff :
  ∀ {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]
    (K : DerivedCategory 𝒜),
    (DerivedCategory.TStructure.t.minus : ObjectProperty (DerivedCategory 𝒜)) K ↔
      ∃ n : ℤ, ∀ i > n, Limits.IsZero ((DerivedCategory.homologyFunctor 𝒜 i).obj K))
@[stacks 03T5] #check (@CategoryTheory.DerivedCategory.bounded_iff :
  ∀ {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]
    (K : DerivedCategory 𝒜),
    (DerivedCategory.TStructure.t.bounded : ObjectProperty (DerivedCategory 𝒜)) K ↔
      (∃ a : ℤ, ∀ i < a, Limits.IsZero ((DerivedCategory.homologyFunctor 𝒜 i).obj K)) ∧
      (∃ b : ℤ, ∀ i > b, Limits.IsZero ((DerivedCategory.homologyFunctor 𝒜 i).obj K)))
