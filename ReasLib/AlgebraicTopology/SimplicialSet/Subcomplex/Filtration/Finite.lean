/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialSet.Subcomplex.Filtration
public import Mathlib.SetTheory.Cardinal.Finite

/-!
@stack 018S

# Finite filtrations by missing simplices

This file isolates the finiteness and cardinality layer used to construct a finite
single-simplex filtration. The underlying attachment-valued filtration API does not depend on
these imports.
-/

@[expose] public section

open CategoryTheory

universe u

namespace SSet.Subcomplex

variable {V : SSet.{u}}

namespace N

/-- The missing nondegenerate simplices of a subcomplex of a finite simplicial set form a
finite type. -/
@[stacks 018S "finiteness of missing nondegenerate simplices"]
instance finite (U : V.Subcomplex) [V.Finite] : Finite U.N := sorry

/-- A finite nonempty type of missing simplices has a simplex of minimal dimension. -/
@[stacks 018S "existence of a minimal-dimensional missing simplex"]
theorem exists_isMinDim (U : V.Subcomplex) [Finite U.N] (hU : Nonempty U.N) :
    ∃ x : U.N, x.IsMinDim := sorry

/-- Adjoining a missing simplex strictly decreases the number of missing nondegenerate
simplices. -/
@[stacks 018S "cardinality decrease after adjoining a missing simplex"]
theorem adjoinCard_lt (x : U.N) [Finite U.N] :
    Nat.card (U ⊔ Subcomplex.ofSimplex x.simplex).N < Nat.card U.N := sorry

/-- The type of missing nondegenerate simplices is empty exactly when the subcomplex is the
whole simplicial set. -/
@[stacks 018S "top subcomplex characterized by missing simplices"]
theorem isEmpty_iff_eq_top (U : V.Subcomplex) :
    IsEmpty U.N ↔ U = ⊤ := sorry

end N

namespace singleSimplex

/-- Every subcomplex of a finite simplicial set admits an attachment-valued finite filtration to
the whole simplicial set. -/
@[stacks 018S "filtration by single-simplex extensions"]
theorem existsFiltration {V : SSet.{u}} [V.Finite]
    (U : V.Subcomplex) :
    ∃ F : Filtration V,
      F.head = U ∧ F.last = (⊤ : V.Subcomplex) := sorry

/-- The proposition-valued relation-series form of the finite single-simplex filtration
theorem. -/
@[stacks 018S "relation-series form of the single-simplex filtration"]
theorem existsRelSeries {V : SSet.{u}} [V.Finite]
    (U : V.Subcomplex) :
    ∃ s : RelSeries (singleSimplex.extensionRel V),
      s.head = U ∧ s.last = (⊤ : V.Subcomplex) := sorry

end singleSimplex

end SSet.Subcomplex
