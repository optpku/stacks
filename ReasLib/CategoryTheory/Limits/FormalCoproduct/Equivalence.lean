/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Basic

/-!
# Equivalence of indexed families

Combinatorial equivalence identifies component objects after reindexing in both
directions. Tautological equivalence instead identifies them up to isomorphism.
-/

@[expose] public section

universe w w₁ w₂ v u

namespace CategoryTheory.Limits.FormalCoproduct

variable {C : Type u} [Category.{v} C]

/-- Two formal coproducts are combinatorially equivalent when reindexings in both
directions identify their component objects. The index universes may differ. -/
def CombinatoriallyEquivalent (𝒰 : FormalCoproduct.{w₁} C)
    (𝒱 : FormalCoproduct.{w₂} C) : Prop :=
  ∃ α : 𝒰.I → 𝒱.I, ∃ β : 𝒱.I → 𝒰.I,
    (∀ i : 𝒰.I, 𝒰.obj i = 𝒱.obj (α i)) ∧
      ∀ j : 𝒱.I, 𝒱.obj j = 𝒰.obj (β j)

/-- Two formal coproducts are tautologically equivalent when reindexings in both
directions identify their component objects up to isomorphism. The index universes
may differ. -/
def TautologicallyEquivalent (𝒰 : FormalCoproduct.{w₁} C)
    (𝒱 : FormalCoproduct.{w₂} C) : Prop :=
  ∃ α : 𝒰.I → 𝒱.I, ∃ β : 𝒱.I → 𝒰.I,
    (∀ i : 𝒰.I, Nonempty (𝒰.obj i ≅ 𝒱.obj (α i))) ∧
      ∀ j : 𝒱.I, Nonempty (𝒱.obj j ≅ 𝒰.obj (β j))

/-- Tautological equivalence is characterized by componentwise-isomorphic maps in both
directions. -/
theorem tautologicallyEquivalent_iff {𝒰 𝒱 : FormalCoproduct.{w} C} :
    TautologicallyEquivalent 𝒰 𝒱 ↔
      ∃ f : 𝒰 ⟶ 𝒱, ∃ g : 𝒱 ⟶ 𝒰,
        (∀ i : 𝒰.I, IsIso (f.φ i)) ∧ ∀ j : 𝒱.I, IsIso (g.φ j) := sorry

end CategoryTheory.Limits.FormalCoproduct
