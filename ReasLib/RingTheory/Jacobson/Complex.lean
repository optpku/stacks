module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.Data.Complex.Basic

@[expose] public section

universe u

namespace Algebra.FiniteType

/-- A finite-type field algebra over `ℂ` has bijective scalar map from `ℂ`. -/
theorem algebraMap_bijective_complex_of_isField
    (R : Type u) [Field R] [Algebra ℂ R] [Algebra.FiniteType ℂ R] :
    Function.Bijective (algebraMap ℂ R) := sorry

end Algebra.FiniteType
