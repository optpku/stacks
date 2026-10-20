/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.BoundedReplacement.LE.Functor

/-!
# Isomorphism transport for good upper truncation

The universal lift construction sends an isomorphism of filtered complexes to an isomorphism of
the truncated map and of every degree component.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.FilteredComplex.TruncLE

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K L : FilteredComplex A}

/-- The good upper-truncation map is an isomorphism when its input map is. -/
@[stacks 05S5 "isomorphism of good upper truncation maps"]
noncomputable instance map_isIso (f : K ⟶ L) (b : ℤ) [IsIso f] :
    IsIso (map f b) := sorry

/-- Every degree component of a good upper-truncation map is an isomorphism. -/
@[stacks 05S5 "isomorphism on good upper truncation components"]
noncomputable instance map_f_isIso (f : K ⟶ L) (b n : ℤ) [IsIso f] :
    IsIso ((map f b).f n) := sorry

variable (f : K ⟶ L) [IsIso f]
#synth IsIso (map f 0)
#synth IsIso ((map f 0).f 0)

end CategoryTheory.FilteredComplex.TruncLE
