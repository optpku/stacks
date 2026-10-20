module

public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplicesSubcomplex
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Missing nondegenerate simplices of a subcomplex

This file develops the order-theoretic API for the type `SSet.Subcomplex.N` of nondegenerate
simplices missing from a subcomplex. It is independent of finite filtrations and pushout
arguments.
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

universe u

namespace SSet.Subcomplex.N

variable {V : SSet.{u}} {U W : V.Subcomplex}

/-- The boundary of the missing simplex `x` is already contained in the subcomplex `U`. -/
@[stacks 018S "boundary of a missing simplex lies in the subcomplex"]
abbrev boundaryRangeLE (x : U.N) : Prop :=
  Subcomplex.range (∂Δ[x.dim].ι ≫ yonedaEquiv.symm x.simplex) ≤ U

/-- A simplex missing from a larger subcomplex is also missing from any smaller subcomplex. -/
theorem notMem_ofLE (h : U ≤ W) (x : W.N) :
    x.simplex ∉ U.obj _ := sorry

/-- Regard a nondegenerate simplex missing from `W` as one missing from `U`, when `U ≤ W`. -/
@[stacks 018S "restriction of a missing simplex along subcomplex inclusion"]
def restrictOfLE (h : U ≤ W) (x : W.N) : U.N :=
  N.mk' x.toN (notMem_ofLE h x)

/-- Restriction along a subcomplex inclusion preserves the underlying nondegenerate simplex. -/
@[simp]
theorem restrictOfLE.toN (h : U ≤ W) (x : W.N) :
    (restrictOfLE h x).toN = x.toN := sorry

/-- Restriction of missing simplices along a subcomplex inclusion is injective. -/
theorem restrictOfLE.injective (h : U ≤ W) :
    Function.Injective (restrictOfLE h) := sorry

/-- The canonical embedding from simplices missing from a larger subcomplex to those missing
from a smaller subcomplex. -/
@[stacks 018S "embedding of missing simplices along subcomplex inclusion"]
def embeddingOfLE (h : U ≤ W) : W.N ↪ U.N :=
  ⟨restrictOfLE h, restrictOfLE.injective h⟩

/-- The embedding of missing simplices induced by adjoining `x` to `U`. -/
@[stacks 018S "embedding after adjoining a missing simplex"]
def adjoinEmbedding (x : U.N) :
    (U ⊔ Subcomplex.ofSimplex x.simplex).N ↪ U.N :=
  embeddingOfLE le_sup_left

/-- The adjoin embedding misses the simplex that has just been adjoined. -/
@[stacks 018S "adjoin embedding is not surjective"]
theorem adjoinEmbedding_not_surjective (x : U.N) :
    ¬ Function.Surjective x.adjoinEmbedding := sorry

/-- A missing simplex has minimal dimension among all simplices missing from the same
subcomplex. -/
@[stacks 018S "minimal dimension among missing simplices"]
def IsMinDim (x : U.N) : Prop :=
  ∀ y : U.N, x.dim ≤ y.dim

namespace IsMinDim

/-- A missing simplex of minimal dimension has its entire boundary in the subcomplex. -/
@[stacks 018S "boundary of a minimal-dimensional missing simplex"]
theorem boundaryRangeLE {x : U.N} (h : x.IsMinDim) :
    x.boundaryRangeLE := sorry

end IsMinDim

end SSet.Subcomplex.N
