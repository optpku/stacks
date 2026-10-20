module

public import ReasLib.LinearAlgebra.Matrix.MinorIdeal.LeftInverse
public import ReasLib.RingTheory.Extension.Presentation.Jacobian

/-!
# Scalar left inverses for presentation Jacobians

This leaf specializes the determinantal-ideal left-inverse API to an arbitrary
finite family of relation rows in a presentation Jacobian.  It has no
standard-smooth or standard-element hypotheses.
-/

@[expose] public section

open scoped Matrix

universe u v w t

namespace Algebra.Presentation.Jacobian

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable {ι : Type w} {σ : Type t} [Fintype ι]
variable {c : ℕ}

/-- The selected relation rows of the Jacobian matrix, evaluated in the target
algebra. -/
@[stacks 07ET]
noncomputable def rows
    (P : Presentation R A ι σ) (r : Fin c ↪ σ) : Matrix (Fin c) ι A :=
  fun j i ↦ target P (r j) i

/-- The Jacobian ideal of selected relation rows is the maximal-minor ideal of
the transposed evaluated row matrix. -/
@[stacks 07ET]
theorem minorIdeal_eq
    (P : Presentation R A ι σ) (r : Fin c ↪ σ) :
    P.jacobianIdeal r = Matrix.minorIdeal c ((rows P r)ᵀ) := sorry

/-- Membership in a selected-row Jacobian ideal gives a scalar left inverse of
the transposed evaluated row matrix. -/
@[stacks 07ET]
theorem exists_leftInverse
    (P : Presentation R A ι σ) (r : Fin c ↪ σ) {a : A}
    (ha : a ∈ P.jacobianIdeal r) :
    ∃ B : Matrix (Fin c) ι A, B * (rows P r)ᵀ = a • 1 := sorry

/-- A scalar left inverse of the transposed evaluated row matrix places the
corresponding scalar power in the selected-row Jacobian ideal. -/
@[stacks 07ET]
theorem leftInverse_pow_mem
    (P : Presentation R A ι σ) (r : Fin c ↪ σ) {a : A}
    (hB : ∃ B : Matrix (Fin c) ι A, B * (rows P r)ᵀ = a • 1) :
    a ^ c ∈ P.jacobianIdeal r := sorry

end Algebra.Presentation.Jacobian
