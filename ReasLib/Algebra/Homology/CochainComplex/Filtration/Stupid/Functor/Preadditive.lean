module

public import ReasLib.Algebra.Homology.CochainComplex.Filtration.Stupid.Functor
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Additivity of the stupid-filtration functor

The canonical stupid filtration is functorial and additive in a cochain
complex.  This support leaf registers that property without mixing it into
the filtration data owner.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.CochainComplex.Stupid

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Equipping cochain complexes with their stupid filtration is additive. -/
@[stacks 0D8Z]
noncomputable instance functor_additive :
    (functor (A := A)).Additive := sorry

#synth (functor (A := A)).Additive

end CategoryTheory.CochainComplex.Stupid
