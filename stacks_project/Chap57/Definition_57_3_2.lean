/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.SerreFunctor.Structure

import StacksCheckRecall

universe w v u

@[expose] public section

/- Definition 57.3.2: Let `k` be a field and let `𝒯` be a `k`-linear triangulated
category such that `dim_k Hom_𝒯(X, Y) < ∞` for all objects `X` and `Y`. A Serre
functor exists when the equivalent conditions of Lemma 57.3.1 hold; it is a
`k`-linear equivalence `S : 𝒯 ≌ 𝒯` with `k`-linear isomorphisms
`Hom_𝒯(X, Y) ≃ₗ[k] Module.Dual k (Hom_𝒯(Y, S.functor.obj X))` functorial in `X` and `Y`. -/
@[stacks 0FY5]
#check (CategoryTheory.SerreFunctor :
  (k : Type w) → (T : Type u) → [Field k] → [CategoryTheory.Category.{v} T] →
    [CategoryTheory.Preadditive T] → [CategoryTheory.Linear k T] →
    Type (max (max u v) w))
