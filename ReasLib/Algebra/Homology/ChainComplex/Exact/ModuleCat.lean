/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.ChainComplex.Exact

/-!
# Function exactness for chain complexes of modules

This leaf supplies the natural-number chain-complex normalization of categorical exactness to
ordinary exactness of the two adjacent underlying linear maps.
-/

@[expose] public section

open CategoryTheory HomologicalComplex

universe u

namespace HomologicalComplex.ExactAt

variable {R : Type u} [Ring R]

/-- Exactness of a chain complex of `R`-modules is equivalent to exactness of the two adjacent
underlying linear maps, including degree zero. -/
@[stacks 00N1 "function exactness in a chain degree"]
theorem function_exact_iff
    (K : ChainComplex (ModuleCat R) ℕ) {j : ℕ} :
    K.ExactAt j ↔ Function.Exact (K.d (j + 1) j).hom (K.d j (j - 1)).hom := sorry

/-- In an exact chain degree, a zero next term makes the outgoing differential injective. -/
@[stacks 00N1 "injectivity from exactness and a zero next term"]
theorem d_injective_of_isZero_next
    (K : ChainComplex (ModuleCat R) ℕ) {j : ℕ}
    (h : K.ExactAt j) (hzero : CategoryTheory.Limits.IsZero (K.X (j + 1))) :
    Function.Injective (K.d j (j - 1)).hom := sorry

end HomologicalComplex.ExactAt
