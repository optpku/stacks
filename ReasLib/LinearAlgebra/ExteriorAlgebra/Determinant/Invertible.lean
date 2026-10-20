/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.ExteriorAlgebra.Determinant.Basic
public import ReasLib.RingTheory.PicardGroup.Invertible
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Invertibility of determinant submodules

The exterior-algebra annihilator is the canonical determinant-line owner. For a finite
projective module it is a tensor-invertible module, so downstream code can use the standard
`Module.Invertible` API without rebuilding a local determinant proof.

@stack 0FJA
-/

noncomputable section

universe u v

namespace Module.Determinant

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Remark 15.119.1: the determinant submodule of a finite projective module is invertible. -/
@[stacks 0FJA "finite-projective determinant line is invertible"]
instance instInvertible [Module.Finite R M] [Module.Projective R M] :
    Module.Invertible R (submodule R M) := sorry
-- Proof strategy: refine a finite-projective standard-open cover so that `M` is free of constant
-- rank on each member; identify `det[R](M)` there with the top exterior power, which is free of
-- rank one, and apply `Module.Invertible.of_finiteLocallyFreeOfRank_one` to descend invertibility.

end Module.Determinant

end
