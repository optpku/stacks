/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Filtration.Complex.BoundedReplacement.GE.Functor

/-!
# Isomorphism transport for good lower truncation

The universal descent construction sends an isomorphism of filtered complexes to an isomorphism
of its truncated map and of every degree component.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.FilteredComplex.TruncGE

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K L : FilteredComplex A}

/-- The good lower-truncation map is an isomorphism when its input map is. -/
@[stacks 05S5 "isomorphism of good lower truncation maps"]
noncomputable instance map_isIso (f : K ⟶ L) (a : ℤ) [IsIso f] :
    IsIso (map f a) := sorry

/-- Every degree component of a good lower-truncation map is an isomorphism. -/
@[stacks 05S5 "isomorphism on good lower truncation components"]
noncomputable instance map_f_isIso (f : K ⟶ L) (a n : ℤ) [IsIso f] :
    IsIso ((map f a).f n) := sorry

variable (f : K ⟶ L) [IsIso f]
#synth IsIso (map f 0)
#synth IsIso ((map f 0).f 0)

end CategoryTheory.FilteredComplex.TruncGE
