module

public import ReasLib.RingTheory.Extension.Presentation.BaseChange
public import ReasLib.RingTheory.Extension.Presentation.Jacobian

/-!
# Base change of presentation Jacobians

The rectangular Jacobian matrix, its embedded minors, and its target ideal all
commute with coefficient base change.
-/

@[expose] public section

open scoped TensorProduct

universe u v w t x

namespace Algebra.Presentation

variable {R : Type u} {A : Type v} {R' : Type w}
variable [CommRing R] [CommRing A] [CommRing R']
variable [Algebra R A] [Algebra R R']
variable {ι : Type t} {σ : Type x} {c : ℕ}

namespace JacobianMatrix

/-- The rectangular Jacobian matrix commutes with coefficient base change. -/
theorem baseChange (P : Presentation R A ι σ) :
    (P.baseChange R').jacobianMatrix =
      P.jacobianMatrix.map (MvPolynomial.map (algebraMap R R')) := sorry

end JacobianMatrix

namespace JacobianMinor

/-- Every embedding-indexed Jacobian minor commutes with coefficient base
change. -/
theorem baseChange
    (P : Presentation R A ι σ) (cols : Fin c ↪ ι) (rows : Fin c ↪ σ) :
    (P.baseChange R').jacobianMinor cols rows =
      MvPolynomial.map (algebraMap R R') (P.jacobianMinor cols rows) := sorry

end JacobianMinor

namespace JacobianIdeal

/-- The target Jacobian ideal commutes with coefficient base change. -/
theorem baseChange (P : Presentation R A ι σ) (rows : Fin c ↪ σ) :
    (P.baseChange R').jacobianIdeal rows =
      Ideal.map TensorProduct.includeRight.toRingHom (P.jacobianIdeal rows) := sorry

end JacobianIdeal

namespace Jacobian

/-- The evaluated Jacobian matrix base-changes entrywise by pure tensors. -/
theorem target_baseChange (P : Presentation R A ι σ) (j : σ) (i : ι) :
    target (P.baseChange R') j i = (1 : R') ⊗ₜ[R] target P j i := sorry

end Jacobian

end Algebra.Presentation
