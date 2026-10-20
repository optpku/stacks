/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.ChainComplex.FiniteFree.Coordinates
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Local-ring coordinate consequences

This leaf contains the small local-ring bridges used by matrix arguments on
finite free complexes.  The matrix and rank data remain independent of the
local-ring assumptions; only membership in the maximal ideal is recorded here.
-/

@[expose] public section

universe u

namespace FiniteFreeComplex

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {e : ℕ}

/-- In a local ring, a displayed differential with no unit entry has all entries in the maximal
ideal. -/
@[stacks 00MS "finite-free differential entries in the maximal ideal"]
theorem diffEntry_mem_maximal_of_no_unit
    (C : _root_.FiniteFreeComplex R e)
    (hnoUnit :
      ¬ ∃ i : Fin e, ∃ a : Fin (C.rank i.succ), ∃ b : Fin (C.rank i.castSucc),
        IsUnit (C.diffEntry i a b))
    (i : Fin e) (a : Fin (C.rank i.succ)) (b : Fin (C.rank i.castSucc)) :
    C.diffEntry i a b ∈ IsLocalRing.maximalIdeal R := sorry

end FiniteFreeComplex
