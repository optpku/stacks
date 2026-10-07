module

public import ReasLib.RingTheory.Algebra.Epicenter
public import ReasLib.RingTheory.Algebra.IsEpi.TensorSquare
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Epicenters and algebra epimorphisms

This leaf connects the equalizer object to the existing tensor-square API for
algebra epimorphisms.  The definition of `Algebra.epicenter` itself remains
independent of an epimorphism hypothesis.
-/

@[expose] public section

universe u v

namespace Algebra

variable {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S] [Algebra R S]

/-- The epicenter is the whole algebra exactly when the structure morphism is
an epimorphism of commutative algebras. -/
@[simp, stacks 04VN "epicenter criterion for algebra epimorphisms"]
theorem epicenter_eq_top_iff :
    epicenter (R := R) (S := S) = ⊤ ↔ Algebra.IsEpi R S := by
  rw [epicenter_eq_top_iff_includeLeft_eq_includeRight]
  exact Algebra.IsEpi.iff_includeLeft_eq_includeRight.symm

end Algebra
