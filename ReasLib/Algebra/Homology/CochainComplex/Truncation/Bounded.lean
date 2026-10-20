/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Bounded
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Tactic.CrossRefAttribute

/-!
# Boundedness of good lower truncations

The good lower truncation is strictly bounded below by construction.  This leaf records the
orthogonal support fact that a bounded-above input therefore becomes bounded, so model producers
can use a named property rather than rebuilding the cutoff argument.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Stacks `013H`: a good lower truncation preserves an explicit strict upper support bound. -/
@[stacks 013H "upper support of a good lower truncation"]
theorem truncGE_isStrictlyLE
    (K : CochainComplex C ℤ) {a b : ℤ} (hK : K.IsStrictlyLE b) :
    (K.truncGE a).IsStrictlyLE b := sorry

/-- Stacks `013H`: a good lower truncation of a bounded-above complex is bounded. -/
@[stacks 013H "bounded good lower truncation"]
theorem bounded_truncGE
    (K : CochainComplex C ℤ) (hK : CochainComplex.minus C K) (a : ℤ) :
    CochainComplex.bounded C (K.truncGE a) := sorry

end CochainComplex

end
