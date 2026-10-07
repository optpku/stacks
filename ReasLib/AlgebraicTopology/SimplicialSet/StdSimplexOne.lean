module

public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplexOne
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The standard simplicial one-simplex

Small computational support for the canonical enumeration of the simplices of `Δ[1]`.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped Simplicial

noncomputable section

universe u v

namespace SSet.stdSimplex

/-- The canonical equivalence between `Fin (n + 2)` and the `n`-simplices of `Δ[1]`. -/
@[stacks 019L "simplices of the simplicial interval"]
noncomputable def objMk₁Equiv (n : ℕ) :
    Fin (n + 2) ≃ (Δ[1] : SSet.{u}).obj (op ⦋n⦌) :=
  (SimplexCategory.toMk₁Equiv (n := n)).trans
    (objEquiv.{u} (n := ⦋1⦌) (m := op ⦋n⦌)).symm

/-- The forward map of `objMk₁Equiv` is the standard `objMk₁` enumeration. -/
@[simp, stacks 019L "standard enumeration equivalence formula"]
theorem objMk₁Equiv.apply (n : ℕ) (i : Fin (n + 2)) :
    objMk₁Equiv.{u} n i = objMk₁ i := sorry

/-- Applying the inverse standard enumeration to an enumerated simplex recovers its index. -/
@[simp, stacks 019L "inverse standard enumeration formula"]
theorem objMk₁Equiv.symm_apply.objMk₁ (n : ℕ) (i : Fin (n + 2)) :
    (objMk₁Equiv.{u} n).symm (objMk₁ i) = i := sorry

/-- Eliminate an `n`-simplex of `Δ[1]` into its zero endpoint, one endpoint, or one of the
`n` interior cut positions. -/
@[stacks 019L "three-way elimination for simplices of the simplicial interval"]
noncomputable def objMk₁Cases {n : ℕ} {α : Sort v}
    (zero one : α) (interior : Fin n → α)
    (x : (Δ[1] : SSet.{u}).obj (op ⦋n⦌)) : α :=
  Fin.lastCases zero (Fin.cases one interior) ((objMk₁Equiv n).symm x)

/-- The maximal enumeration index selects the zero endpoint in `objMk₁Cases`. -/
@[simp, stacks 019L "zero endpoint computation for simplicial interval elimination"]
theorem objMk₁Cases.zero {n : ℕ} {α : Sort v}
    (zero one : α) (interior : Fin n → α) :
    objMk₁Cases.{u, v} zero one interior
        (objMk₁ (Fin.last (n + 1))) = zero := sorry

/-- The zero enumeration index selects the one endpoint in `objMk₁Cases`. -/
@[simp, stacks 019L "one endpoint computation for simplicial interval elimination"]
theorem objMk₁Cases.one {n : ℕ} {α : Sort v}
    (zero one : α) (interior : Fin n → α) :
    objMk₁Cases.{u, v} zero one interior
        (objMk₁ (0 : Fin (n + 2))) = one := sorry

/-- A nonendpoint enumeration index selects its corresponding interior cut position in
`objMk₁Cases`. -/
@[simp, stacks 019L "interior computation for simplicial interval elimination"]
theorem objMk₁Cases.interior {n : ℕ} {α : Sort v}
    (zero one : α) (interior : Fin n → α) (i : Fin n) :
    objMk₁Cases.{u, v} zero one interior
        (objMk₁ i.succ.castSucc) = interior i := sorry

end SSet.stdSimplex
