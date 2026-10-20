module

public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Bases in finite products of fields

The product-of-fields step is kept independent from semilocal-ring reduction.
It is the reusable linear-algebra core of the simultaneous-generator argument.
-/

@[expose] public section

universe u v w

namespace Module.Basis

/-- A `k`-subspace spanning a finite product of field-valued free modules contains a basis over the
product ring. -/
@[stacks 03C1 "basis inside a spanning subspace of a product of fields"]
theorem exists_mem_of_span_eq_top_pi
    {k : Type u} [Field k] [Infinite k]
    {ι : Type v} {K : ι → Type w}
    [Finite ι] [∀ i, Field (K i)] [∀ i, Algebra k (K i)]
    {n : ℕ}
    (N : Submodule k (∀ i, Fin n → K i))
    (hN : Submodule.span (∀ i, K i) (N : Set (∀ i, Fin n → K i)) = ⊤) :
    ∃ b : Module.Basis (Fin n) (∀ i, K i) (∀ i, Fin n → K i),
      ∀ j, b j ∈ N := sorry

end Module.Basis
