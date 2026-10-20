module

public import ReasLib.NumberTheory.Automorphic.RamifiedLanglands
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
open CategoryTheory Matrix Matrix.GeneralLinearGroup TopologicalSpace

universe u

/- Remark 64.31.4. The global Langlands existence theorems extend to positive
rank with ramification over function fields of curves over finite fields. -/
@[stacks 03VV] #check (AlgebraicGeometry.SchemeOverField.exists_galoisRepresentation_of_eigenformGL :
  ∀ {k : Type u} [Field k]
    (X : SchemeOverField k) [Curve X] [Smooth X.hom] [Projective X.hom]
    [GeometricallyIrreducible X.hom] [Finite k] {p ℓ : ℕ}
    [Fact p.Prime] [CharP k p] [Fact ℓ.Prime] [ConnectedSpace X.left],
    ∀ {n : ℕ} (hn : 0 < n) (hℓ : ℓ ≠ p)
    (U : X.left.Opens) [Nonempty U] [ConnectedSpace (restrictOpen X U).left]
    (xbar : GeometricPoint (restrictOpen X U).left)
    (φ : CuspFormGL X n U (PadicAlgCl ℓ))
    (f : EigenformGL X n U (PadicAlgCl ℓ))
    (hφ : IsEigenformGL X n U φ f)
    (h_lambda : EigenformGL.lambda_last_is_integral_unit f),
    ∃ (E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ))
      (hE : FiniteDimensional ℚ_[ℓ] E)
      (ρ : etaleFundamentalGroup (restrictOpen X U).left xbar →ₜ* GL (Fin n) E),
      IsAbsolutelyIrreducible ρ.toMonoidHom ∧ f.IsAttachedTo ρ)

#check (AlgebraicGeometry.SchemeOverField.exists_eigenformGL_of_galoisRepresentation :
  ∀ {k : Type u} [Field k]
    (X : SchemeOverField k) [Curve X] [Smooth X.hom] [Projective X.hom]
    [GeometricallyIrreducible X.hom] [Finite k] {p ℓ : ℕ}
    [Fact p.Prime] [CharP k p] [Fact ℓ.Prime] [ConnectedSpace X.left],
    ∀ {n : ℕ} (hn : 0 < n) (hℓ : ℓ ≠ p)
    (U : X.left.Opens) [Nonempty U] [ConnectedSpace (restrictOpen X U).left]
    (xbar : GeometricPoint (restrictOpen X U).left)
    (E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ))
    [FiniteDimensional ℚ_[ℓ] E]
    (ρ : etaleFundamentalGroup (restrictOpen X U).left xbar →ₜ* GL (Fin n) E)
    (hρ : IsAbsolutelyIrreducible ρ.toMonoidHom),
    ∃ (φ : CuspFormGL X n U (PadicAlgCl ℓ))
      (f : EigenformGL X n U (PadicAlgCl ℓ)),
      IsEigenformGL X n U φ f ∧
        EigenformGL.lambda_last_is_integral_unit f ∧ f.IsAttachedTo ρ)
