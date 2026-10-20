/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
public import ReasLib.Algebra.Homology.CochainComplex.FiniteProjective

@[expose] public section

universe u

namespace CochainComplex.IsBoundedFiniteProjective

variable {R : Type u} [Ring R]

/-- Every bounded finite-projective cochain complex is K-projective. -/
instance isKProjective (P : CochainComplex (ModuleCat R) ℤ)
    [P.IsBoundedFiniteProjective] : P.IsKProjective := sorry

end CochainComplex.IsBoundedFiniteProjective
