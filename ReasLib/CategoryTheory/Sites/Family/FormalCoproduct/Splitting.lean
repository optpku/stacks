/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Splitting
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Splitting.Monic
public import ReasLib.CategoryTheory.Limits.FormalCoproduct.Componentwise
public import ReasLib.CategoryTheory.Sites.Family.FormalCoproduct
import Mathlib.Tactic.CrossRefAttribute

/-!
# Splittings of simplicial semi-representable families

For diagrams of formal coproducts, splitness is detected componentwise on surjections in the
simplex category. Since every such surjection is a composite of degeneracies, it is enough to
test the standard degeneracy operators. Both truncated and untruncated APIs are provided.
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Opposite
open SimplexCategory
open scoped CategoryTheory.SemiRepresentableFamily Simplicial SimplexCategory.Truncated
open Limits.FormalCoproduct
open Limits.FormalCoproduct.Componentwise

namespace SimplicialObject.Truncated.Componentwise

open SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]

/-- The component morphism induced by a degeneracy operator of a truncated simplicial
semi-representable family. -/
@[stacks 0DAU "truncated degeneracy component map"]
abbrev degeneracyMap {n m : ℕ}
    (K : SimplicialObject.Truncated (SR(C)) n) (hm : m < n) (j : Fin (m + 1))
    (a : (K _⦋m,Nat.le_of_lt hm⦌ₙ).index) :
    (K _⦋m,Nat.le_of_lt hm⦌ₙ).obj a ⟶
      (K _⦋m + 1,Nat.succ_le_of_lt hm⦌ₙ).obj
        (componentIndex K
          (SimplexCategory.Truncated.σ n j
            (Nat.succ_le_of_lt hm) (Nat.le_of_lt hm)) a) :=
  componentMap K
    (SimplexCategory.Truncated.σ n j (Nat.succ_le_of_lt hm) (Nat.le_of_lt hm)) a

/-- The truncated degeneracy component map is the corresponding component of the diagram
morphism. -/
@[simp]
theorem degeneracyMap_eq_componentMap {n m : ℕ}
    (K : SimplicialObject.Truncated (SR(C)) n) (hm : m < n) (j : Fin (m + 1))
    (a : (K _⦋m,Nat.le_of_lt hm⦌ₙ).index) :
    degeneracyMap K hm j a =
      componentMap K
        (SimplexCategory.Truncated.σ n j
          (Nat.succ_le_of_lt hm) (Nat.le_of_lt hm)) a := sorry

/-- Every component map induced by a truncated degeneracy operator is an isomorphism. -/
@[stacks 0DAU "componentwise isomorphisms on truncated degeneracies"]
def IsoOnDegeneracies {n : ℕ}
    (K : SimplicialObject.Truncated (SR(C)) n) : Prop :=
  ∀ ⦃m : ℕ⦄ (hm : m < n) (j : Fin (m + 1))
    (a : (K _⦋m,Nat.le_of_lt hm⦌ₙ).index),
    CategoryTheory.IsIso (degeneracyMap K hm j a)

/-- The truncated degeneracy criterion is the pointwise isomorphism condition on the standard
degeneracy component maps. -/
@[simp]
theorem isoOnDegeneracies_iff {n : ℕ}
    (K : SimplicialObject.Truncated (SR(C)) n) :
    IsoOnDegeneracies K ↔
      ∀ ⦃m : ℕ⦄ (hm : m < n) (j : Fin (m + 1))
        (a : (K _⦋m,Nat.le_of_lt hm⦌ₙ).index),
        CategoryTheory.IsIso (degeneracyMap K hm j a) := sorry

/-- Under the truncated degeneracy criterion, every degeneracy component map is an
isomorphism. -/
theorem IsoOnDegeneracies.component
    {n : ℕ} {K : SimplicialObject.Truncated (SR(C)) n}
    (hK : IsoOnDegeneracies K) {m : ℕ} (hm : m < n) (j : Fin (m + 1))
    (a : (K _⦋m,Nat.le_of_lt hm⦌ₙ).index) :
    CategoryTheory.IsIso (degeneracyMap K hm j a) := sorry

/-- Lemma 25.12.1 (1) (0DAU): a truncated simplicial semi-representable family is split exactly
when every component map induced by an epimorphism of truncated simplices is an isomorphism. -/
@[stacks 0DAU "truncated split iff epi components"]
theorem isSplit_iff_epis {n : ℕ}
    (K : SimplicialObject.Truncated (SR(C)) n) :
    IsSplit K ↔ IsoOnEpis K := sorry

/-- Lemma 25.12.1 (2) (0DAU): for a truncated simplicial semi-representable family, the
componentwise isomorphism condition on all epimorphisms is equivalent to the condition on the
standard degeneracy operators. -/
@[stacks 0DAU "truncated epi components iff degeneracy components"]
theorem epis_iff_degeneracies {n : ℕ}
    (K : SimplicialObject.Truncated (SR(C)) n) :
    IsoOnEpis K ↔ IsoOnDegeneracies K := sorry

/-- A split truncated simplicial semi-representable family satisfies the componentwise
isomorphism criterion on epimorphisms. -/
theorem epis_of_isSplit {n : ℕ}
    {K : SimplicialObject.Truncated (SR(C)) n} (hK : IsSplit K) :
    IsoOnEpis K := sorry

/-- The componentwise isomorphism criterion on epimorphisms produces a truncated splitting by
subobjects. -/
theorem isSplit_of_epis {n : ℕ}
    {K : SimplicialObject.Truncated (SR(C)) n}
    (hK : IsoOnEpis K) : IsSplit K := sorry

/-- A truncated simplicial semi-representable family is split exactly when all degeneracy
component maps are isomorphisms. -/
theorem isSplit_iff_degeneracies {n : ℕ}
    (K : SimplicialObject.Truncated (SR(C)) n) :
    IsSplit K ↔ IsoOnDegeneracies K := sorry

/-- A split truncated simplicial semi-representable family satisfies the degeneracy
componentwise isomorphism criterion. -/
theorem degeneracies_of_isSplit {n : ℕ}
    {K : SimplicialObject.Truncated (SR(C)) n} (hK : IsSplit K) :
    IsoOnDegeneracies K := sorry

/-- The truncated degeneracy componentwise isomorphism criterion produces a splitting by
subobjects. -/
theorem isSplit_of_degeneracies {n : ℕ}
    {K : SimplicialObject.Truncated (SR(C)) n}
    (hK : IsoOnDegeneracies K) : IsSplit K := sorry

end SimplicialObject.Truncated.Componentwise

namespace SimplicialObject.Componentwise

open SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]

/-- The component morphism induced by a degeneracy operator of a simplicial
semi-representable family. -/
@[stacks 0DAU "degeneracy component map"]
abbrev degeneracyMap (K : SimplicialObject (SR(C)))
    (n : ℕ) (j : Fin (n + 1)) (a : (K _⦋n⦌).index) :
    (K _⦋n⦌).obj a ⟶
      (K _⦋n + 1⦌).obj (componentIndex K (SimplexCategory.σ j) a) :=
  componentMap K (SimplexCategory.σ j) a

/-- The degeneracy component map is the corresponding component of the simplicial diagram
morphism. -/
@[simp]
theorem degeneracyMap_eq_componentMap
    (K : SimplicialObject (SR(C))) (n : ℕ) (j : Fin (n + 1))
    (a : (K _⦋n⦌).index) :
    degeneracyMap K n j a = componentMap K (SimplexCategory.σ j) a := sorry

/-- Every component map induced by a simplicial degeneracy operator is an isomorphism. -/
@[stacks 0DAU "componentwise isomorphisms on degeneracies"]
def IsoOnDegeneracies (K : SimplicialObject (SR(C))) : Prop :=
  ∀ (n : ℕ) (j : Fin (n + 1)) (a : (K _⦋n⦌).index),
    CategoryTheory.IsIso (degeneracyMap K n j a)

/-- The degeneracy criterion is the pointwise isomorphism condition on the standard degeneracy
component maps. -/
@[simp]
theorem isoOnDegeneracies_iff (K : SimplicialObject (SR(C))) :
    IsoOnDegeneracies K ↔
      ∀ (n : ℕ) (j : Fin (n + 1)) (a : (K _⦋n⦌).index),
        CategoryTheory.IsIso (degeneracyMap K n j a) := sorry

/-- Under the degeneracy criterion, every simplicial degeneracy component map is an
isomorphism. -/
theorem IsoOnDegeneracies.component
    {K : SimplicialObject (SR(C))} (hK : IsoOnDegeneracies K)
    (n : ℕ) (j : Fin (n + 1)) (a : (K _⦋n⦌).index) :
    CategoryTheory.IsIso (degeneracyMap K n j a) := sorry

/-- Lemma 25.12.1 (3) (0DAU): a simplicial semi-representable family is split exactly when
every component map induced by an epimorphism of simplices is an isomorphism. -/
@[stacks 0DAU "split iff epi components"]
theorem isSplit_iff_epis (K : SimplicialObject (SR(C))) :
    IsSplit K ↔ IsoOnEpis K := sorry

/-- Lemma 25.12.1 (4) (0DAU): for a simplicial semi-representable family, the componentwise
isomorphism condition on all epimorphisms is equivalent to the condition on the standard
degeneracy operators. -/
@[stacks 0DAU "epi components iff degeneracy components"]
theorem epis_iff_degeneracies (K : SimplicialObject (SR(C))) :
    IsoOnEpis K ↔ IsoOnDegeneracies K := sorry

/-- A split simplicial semi-representable family satisfies the componentwise isomorphism
criterion on epimorphisms. -/
theorem epis_of_isSplit {K : SimplicialObject (SR(C))} (hK : IsSplit K) :
    IsoOnEpis K := sorry

/-- The componentwise isomorphism criterion on epimorphisms produces a simplicial splitting by
subobjects. -/
theorem isSplit_of_epis {K : SimplicialObject (SR(C))}
    (hK : IsoOnEpis K) : IsSplit K := sorry

/-- A simplicial semi-representable family is split exactly when all degeneracy component maps
are isomorphisms. -/
theorem isSplit_iff_degeneracies (K : SimplicialObject (SR(C))) :
    IsSplit K ↔ IsoOnDegeneracies K := sorry

/-- A split simplicial semi-representable family satisfies the degeneracy componentwise
isomorphism criterion. -/
theorem degeneracies_of_isSplit {K : SimplicialObject (SR(C))} (hK : IsSplit K) :
    IsoOnDegeneracies K := sorry

/-- The degeneracy componentwise isomorphism criterion produces a simplicial splitting by
subobjects. -/
theorem isSplit_of_degeneracies
    {K : SimplicialObject (SR(C))} (hK : IsoOnDegeneracies K) : IsSplit K := sorry

end SimplicialObject.Componentwise

end CategoryTheory
