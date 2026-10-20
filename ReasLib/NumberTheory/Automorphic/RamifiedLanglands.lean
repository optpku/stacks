module

public import Mathlib.Topology.Algebra.IntermediateField
public import ReasLib.NumberTheory.Automorphic.RamifiedEigenform
public import ReasLib.RepresentationTheory.Matrix

/-!
# Ramified global Langlands existence for general linear groups
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory Matrix
open Finset TopologicalSpace
open scoped RestrictedProduct

universe u v

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]
variable (X : SchemeOverField k)
variable [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]

variable [Finite k]
variable {p ℓ : ℕ} [Fact p.Prime] [CharP k p] [Fact ℓ.Prime]
variable [ConnectedSpace X.left]

/-- An eigenform for `GL (Fin n)` on a nonempty open
`U ⊆ X`, with values in `PadicAlgCl ℓ` and `ℓ ≠ p`, yields a continuous
absolutely irreducible representation `ρ : π₁(U, xbar) →ₜ* GL (Fin n) E` on a
finite extension `E` of `ℚ_[ℓ]` contained in `PadicAlgCl ℓ`, matching Frobenius
characteristic polynomials at every closed point of `U`. -/
theorem exists_galoisRepresentation_of_eigenformGL {n : ℕ} (hn : 0 < n) (hℓ : ℓ ≠ p)
    (U : X.left.Opens) [Nonempty U] [ConnectedSpace (restrictOpen X U).left]
    (xbar : GeometricPoint (restrictOpen X U).left)
    (φ : CuspFormGL X n U (PadicAlgCl ℓ))
    (f : EigenformGL X n U (PadicAlgCl ℓ))
    (hφ : IsEigenformGL X n U φ f)
    (h_lambda : EigenformGL.lambda_last_is_integral_unit f) :
    ∃ (E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ))
      (hE : FiniteDimensional ℚ_[ℓ] E)
      (ρ : etaleFundamentalGroup (restrictOpen X U).left xbar →ₜ* GL (Fin n) E),
      GeneralLinearGroup.IsAbsolutelyIrreducible ρ.toMonoidHom ∧ f.IsAttachedTo ρ := sorry

/-- A continuous absolutely irreducible representation
`ρ : π₁(U, xbar) →ₜ* GL (Fin n) E` on a finite extension `E` of `ℚ_[ℓ]`
contained in `PadicAlgCl ℓ`, with `ℓ ≠ p`, yields an eigenform for
`GL (Fin n)` on the nonempty open `U ⊆ X` whose Frobenius characteristic
polynomials match those of `ρ` at every closed point of `U`. -/
theorem exists_eigenformGL_of_galoisRepresentation {n : ℕ} (hn : 0 < n) (hℓ : ℓ ≠ p)
    (U : X.left.Opens) [Nonempty U] [ConnectedSpace (restrictOpen X U).left]
    (xbar : GeometricPoint (restrictOpen X U).left)
    (E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ))
    [FiniteDimensional ℚ_[ℓ] E]
    (ρ : etaleFundamentalGroup (restrictOpen X U).left xbar →ₜ* GL (Fin n) E)
    (hρ : GeneralLinearGroup.IsAbsolutelyIrreducible ρ.toMonoidHom) :
    ∃ (φ : CuspFormGL X n U (PadicAlgCl ℓ))
      (f : EigenformGL X n U (PadicAlgCl ℓ)),
      IsEigenformGL X n U φ f ∧
        EigenformGL.lambda_last_is_integral_unit f ∧ f.IsAttachedTo ρ := sorry


end AlgebraicGeometry.SchemeOverField
