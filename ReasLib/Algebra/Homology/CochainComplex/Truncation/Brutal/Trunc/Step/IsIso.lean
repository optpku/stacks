/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.Truncation.Brutal.Trunc.Step

/-!
# Isomorphism transport for brutal truncation pieces

The single-complex piece exposed at each brutal cutoff transports
isomorphisms of cochain complexes.  This leaf keeps that fact available to
short-exact-sequence and Postnikov clients without rebuilding the single
complex map.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.CochainComplex.Brutal.Trunc.Piece

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K L : CochainComplex A ℤ}

/-- A cutoff-piece map is an isomorphism when the inducing cochain map is. -/
@[stacks 0D8Z]
noncomputable instance map_isIso (f : K ⟶ L) (n : ℕ) [IsIso f] :
    IsIso (map f n) := sorry

/-- Every degree component of a cutoff-piece map is an isomorphism when the inducing map is. -/
@[stacks 0D8Z]
noncomputable instance map_f_isIso (f : K ⟶ L) (n : ℕ) (i : ℤ) [IsIso f] :
    IsIso ((map f n).f i) := sorry

variable (f : K ⟶ L) [IsIso f]
#synth IsIso (map f 0)
#synth IsIso ((map f 0).f 0)

end CategoryTheory.CochainComplex.Brutal.Trunc.Piece
