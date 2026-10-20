module

public import Mathlib.AlgebraicTopology.SimplicialObject.Split
public import ReasLib.AlgebraicTopology.SimplexCategory.Truncated.EpiMono
import Mathlib.Tactic.CrossRefAttribute

/-!
# Indices for splittings of truncated simplicial objects

This leaf refines Mathlib's surjection indices by recording the bounded degree and the associated
morphism in the truncated simplex category.
-/

@[expose] public section

open CategoryTheory Opposite
open SimplexCategory SimplexCategory.Truncated SimplexCategory.Truncated.Hom
open scoped SimplexCategory.Truncated

namespace CategoryTheory.SimplicialObject.Truncated.Splitting

/-- The surjections indexing the canonical decomposition of a truncated simplex. -/
@[stacks 017P "truncated splitting index set"]
abbrev IndexSet {n : ℕ} (Δ : (SimplexCategory.Truncated n)ᵒᵖ) :=
  SimplicialObject.Splitting.IndexSet (op Δ.unop.obj)

namespace IndexSet

variable {n : ℕ} {Δ : (SimplexCategory.Truncated n)ᵒᵖ} (A : IndexSet Δ)

/-- The codomain degree of a surjection indexing a truncated splitting is still at most the
truncation bound. -/
@[stacks 017P "truncated splitting summand bound"]
theorem len_le : A.1.unop.len ≤ n := sorry

/-- The truncated degree of the summand indexed by `A`. -/
@[stacks 017P "truncated splitting summand degree"]
def degree : Fin (n + 1) :=
  ⟨A.1.unop.len, Nat.lt_succ_of_le A.len_le⟩

/-- The value of the truncated degree selected by a surjection index. -/
@[simp, stacks 017P "truncated splitting summand degree value"]
theorem degree_val : A.degree.1 = A.1.unop.len := sorry

/-- The truncated simplex morphism underlying the surjection index `A`. Its target is exposed
through the semantic degree API rather than a raw length-and-bound pair. -/
@[stacks 017P "truncated splitting summand map"]
abbrev map : Δ.unop ⟶ ⦋A.degree⦌ₙ :=
  tr A.e Δ.unop.property A.len_le

/-- The underlying simplex-category morphism of `A.map` is the surjection represented by
`A`. -/
@[simp, stacks 017P "underlying truncated splitting summand map"]
theorem map_hom : A.map.hom = A.e := sorry

/-- The truncated morphism represented by a splitting index is an epimorphism. -/
@[stacks 017P "epimorphic truncated splitting summand map"]
instance map_epi : Epi A.map := sorry

/-- The identity surjection as an index of the splitting decomposition at `Δ`. -/
@[stacks 017P "identity truncated splitting index"]
def id (Δ : (SimplexCategory.Truncated n)ᵒᵖ) : IndexSet Δ :=
  SimplicialObject.Splitting.IndexSet.id (op Δ.unop.obj)

/-- The identity index in degree `m` selects degree `m`. -/
@[simp, stacks 017P "degree of the identity truncated splitting index"]
theorem degree_id (m : Fin (n + 1)) :
    (id (op ⦋m⦌ₙ)).degree = m := sorry

/-- The truncated morphism represented by the identity index is the identity. -/
@[simp, stacks 017P "map of the identity truncated splitting index"]
theorem map_id (m : Fin (n + 1)) :
    (id (op ⦋m⦌ₙ)).map = 𝟙 ⦋m⦌ₙ := sorry

/-- Precompose a splitting index by an epimorphism in the opposite truncated simplex category. -/
@[stacks 017P "composition of truncated splitting indices"]
def epiComp {Δ₁ Δ₂ : (SimplexCategory.Truncated n)ᵒᵖ} (A : IndexSet Δ₁)
    (p : Δ₁ ⟶ Δ₂) [Epi p.unop] : IndexSet Δ₂ :=
  SimplicialObject.Splitting.IndexSet.epiComp A p.unop.hom.op

/-- Precomposition by an epimorphism does not change the selected summand degree. -/
@[simp, stacks 017P "degree after composing truncated splitting indices"]
theorem degree_epiComp {Δ₁ Δ₂ : (SimplexCategory.Truncated n)ᵒᵖ} (A : IndexSet Δ₁)
    (p : Δ₁ ⟶ Δ₂) [Epi p.unop] :
    (A.epiComp p).degree = A.degree := sorry

/-- The summand map represented after precomposition is the corresponding composite. -/
@[simp, stacks 017P "map after composing truncated splitting indices"]
theorem epiComp_map {Δ₁ Δ₂ : (SimplexCategory.Truncated n)ᵒᵖ} (A : IndexSet Δ₁)
    (p : Δ₁ ⟶ Δ₂) [Epi p.unop] :
    (A.epiComp p).map = p.unop ≫ A.map := sorry

end IndexSet

end CategoryTheory.SimplicialObject.Truncated.Splitting
