module

public import ReasLib.CategoryTheory.Filtration.Complex.BoundedReplacement.GE.Functor
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Additivity of good lower truncation

The functorial good lower truncation is additive in an abelian coefficient category.  This support
leaf keeps the transport instance independent of boundedness and quasi-isomorphism criteria.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.FilteredComplex.TruncGE

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Good lower truncation at a fixed cutoff preserves addition of filtered-complex maps. -/
@[stacks 05S5 "additivity of good lower truncation"]
noncomputable instance functor_additive (a : ℤ) :
    (functor (A := A) a).Additive := sorry

#synth (functor (A := A) 0).Additive

end CategoryTheory.FilteredComplex.TruncGE
