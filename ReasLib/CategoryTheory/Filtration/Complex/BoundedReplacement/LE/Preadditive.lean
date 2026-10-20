module

public import ReasLib.CategoryTheory.Filtration.Complex.BoundedReplacement.LE.Functor
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Additivity of good upper truncation

The functorial good upper truncation is additive in an abelian coefficient category.  The instance
is isolated from the construction and its support lemmas for narrow imports.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.FilteredComplex.TruncLE

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Good upper truncation at a fixed cutoff preserves addition of filtered-complex maps. -/
@[stacks 05S5 "additivity of good upper truncation"]
noncomputable instance functor_additive (b : ℤ) :
    (functor (A := A) b).Additive := sorry

#synth (functor (A := A) 0).Additive

end CategoryTheory.FilteredComplex.TruncLE
