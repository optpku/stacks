module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.SimpleRing.Field

@[expose] public section

universe u v

namespace Subalgebra

/-- The center of a finite-dimensional simple algebra over a field is a finite field extension
of that field. -/
theorem center_finiteFieldExtension
    {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
    [FiniteDimensional k A] [IsSimpleRing A] :
    FiniteDimensional k (center k A) ∧ IsField (center k A) := by
  exact ⟨inferInstance, IsSimpleRing.isField_center A⟩

end Subalgebra
