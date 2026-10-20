/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.BoundedReplacement.Square.Functor

/-!
# Isomorphism transport for bounded replacement squares

The iterated truncation map induced by an isomorphism is an isomorphism at the bounded vertex and
in every cochain degree.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.FilteredComplex.Replace.Square.Bounded

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K L : FilteredComplex A}

/-- The bounded replacement map is an isomorphism when its input map is. -/
@[stacks 05S5 "isomorphism of bounded filtered replacements"]
noncomputable instance map_isIso (f : K ⟶ L) (a b : ℤ) [IsIso f] :
    IsIso (map f a b) := sorry

/-- Every degree component of a bounded replacement map is an isomorphism. -/
@[stacks 05S5 "isomorphism on bounded replacement components"]
noncomputable instance map_f_isIso (f : K ⟶ L) (a b n : ℤ) [IsIso f] :
    IsIso ((map f a b).f n) := sorry

variable (f : K ⟶ L) [IsIso f]
#synth IsIso (map f 0 0)
#synth IsIso ((map f 0 0).f 0)

end CategoryTheory.FilteredComplex.Replace.Square.Bounded
