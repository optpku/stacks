module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Top structure maps of truncated simplicial objects

This file gives a truncated simplicial object the same concise face and degeneracy API as an
ordinary simplicial object.  The maps are taken in the top two degrees, which is the form used by
matching objects and one-step extensions.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped Simplicial SimplexCategory.Truncated

universe u v

namespace CategoryTheory.SimplicialObject.Truncated

variable {C : Type u} [Category.{v} C]

/-- The `i`-th face from the top degree of a successor-truncated simplicial object. -/
@[stacks 0186 "top face of a truncated simplicial object",
  stacks 0188 "top face of a truncated simplicial object"]
def δ {n : ℕ} (U : SimplicialObject.Truncated C (n + 1)) (i : Fin (n + 2)) :
    U _⦋n + 1⦌ₙ₊₁ ⟶ U _⦋n⦌ₙ₊₁ :=
  U.map
    (SimplexCategory.Truncated.Hom.tr (SimplexCategory.δ i)
      (Nat.le_succ n) le_rfl).op

/-- The top face map is the functorial image of the corresponding truncated coface. -/
@[stacks 0186 "top face map formula", stacks 0188 "top face map formula"]
theorem δ_def {n : ℕ} (U : SimplicialObject.Truncated C (n + 1)) (i : Fin (n + 2)) :
    U.δ i =
      U.map
        (SimplexCategory.Truncated.Hom.tr (SimplexCategory.δ i)
          (Nat.le_succ n) le_rfl).op := sorry

/-- A morphism of successor-truncated simplicial objects commutes with every top face map. -/
@[reassoc (attr := simp), stacks 0186 "top face naturality",
  stacks 0188 "top face naturality"]
theorem δ_naturality {n : ℕ} {U V : SimplicialObject.Truncated C (n + 1)}
    (f : U ⟶ V) (i : Fin (n + 2)) :
    U.δ i ≫
        f.app (op ⦋n, Nat.le_succ n⦌ₙ₊₁) =
      f.app (op ⦋n + 1, le_rfl⦌ₙ₊₁) ≫ V.δ i := sorry

/-- The `i`-th degeneracy into the top degree of a successor-truncated simplicial object. -/
@[stacks 0186 "top degeneracy of a truncated simplicial object",
  stacks 0188 "top degeneracy of a truncated simplicial object"]
def σ {n : ℕ} (U : SimplicialObject.Truncated C (n + 1)) (i : Fin (n + 1)) :
    U _⦋n⦌ₙ₊₁ ⟶ U _⦋n + 1⦌ₙ₊₁ :=
  U.map
    (SimplexCategory.Truncated.Hom.tr (SimplexCategory.σ i)
      le_rfl (Nat.le_succ n)).op

/-- The top degeneracy map is the functorial image of the corresponding truncated codegeneracy. -/
@[stacks 0186 "top degeneracy map formula", stacks 0188 "top degeneracy map formula"]
theorem σ_def {n : ℕ} (U : SimplicialObject.Truncated C (n + 1)) (i : Fin (n + 1)) :
    U.σ i =
      U.map
        (SimplexCategory.Truncated.Hom.tr (SimplexCategory.σ i)
          le_rfl (Nat.le_succ n)).op := sorry

/-- A morphism of successor-truncated simplicial objects commutes with every top degeneracy
map. -/
@[reassoc (attr := simp), stacks 0186 "top degeneracy naturality",
  stacks 0188 "top degeneracy naturality"]
theorem σ_naturality {n : ℕ} {U V : SimplicialObject.Truncated C (n + 1)}
    (f : U ⟶ V) (i : Fin (n + 1)) :
    U.σ i ≫
        f.app (op ⦋n + 1, le_rfl⦌ₙ₊₁) =
      f.app (op ⦋n, Nat.le_succ n⦌ₙ₊₁) ≫ V.σ i := sorry

end CategoryTheory.SimplicialObject.Truncated
