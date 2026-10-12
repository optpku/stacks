/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Order.DirectLimit.Tail
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Filtered tail preorders

This leaf records the categorical filteredness of an upper tail of a directed
preorder.  It is the categorical form of the canonical order restriction in
`Set.Ici.isDirectedOrder`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace Set.Ici

variable {I : Type u} [Preorder I]

/-- The preorder category on an upper tail of a directed preorder is filtered. -/
@[stacks 00QV "direct-limit tail"]
instance instIsFiltered [IsDirectedOrder I] (i0 : I) :
    IsFiltered (Set.Ici i0) :=
  CategoryTheory.isFiltered_of_directed_le_nonempty (Set.Ici i0)

end Set.Ici

namespace Set.Ici.Adjoin

variable {I : Type u} [Preorder I]

/-- The right-tail embedding into an adjoined upper-tail preorder is final.

Every original index admits a comparison into the right copy of the anchor,
and every right-tail index already belongs to that final subdiagram. -/
@[stacks 00YO "adjoined directed tail"]
theorem right_final [IsDirected I (· ≤ ·)] (i0 : I) :
    Functor.Final ((right i0).toOrderHom.toFunctor) := sorry

/-- Typeclass access to finality of the right-tail embedding. -/
noncomputable instance instRightFinal [IsDirected I (· ≤ ·)] (i0 : I) :
    Functor.Final ((right i0).toOrderHom.toFunctor) :=
  right_final i0

end Set.Ici.Adjoin
