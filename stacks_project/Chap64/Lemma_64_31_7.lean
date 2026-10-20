module

public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.CompatibleRepresentation
import StacksCheckRecall

/-!
# Switching finite places of an SL(2) representation

An absolutely irreducible continuous `SL(2)` representation of `π₁(X)` over
the completion of a number field at a finite place not above `p` can be
switched to any other such place, up to a finite extension, preserving
geometric-Frobenius characteristic polynomials.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
open IsDedekindDomain Matrix NumberField
open scoped MatrixGroups NumberField

universe u

namespace AlgebraicGeometry.SchemeOverField

/- Lemma 64.31.7. Switching `l`. Let `E` be a number field, and let
`ρ : etaleFundamentalGroup X.left xbar →ₜ* SL(2, ℓ.adicCompletion E)` be
absolutely irreducible and continuous, where `ℓ` is a finite place of `E` not
lying above `p`. Then for any second finite place `ℓ'` of `E` not lying above
`p` there exists a finite extension of `ℓ'.adicCompletion E` carrying an
absolutely irreducible continuous representation
`ρ' : etaleFundamentalGroup X.left xbar →ₜ* SL(2, μ.adicCompletion E')`
compatible with `ρ` in the sense that the characteristic polynomials of all
geometric Frobenii are the same. -/
@[stacks 03VY] #check
  (AlgebraicGeometry.SchemeOverField.exists_compatible_specialLinearRepresentation :
    ∀ {k : Type u} [Field k] [Finite k] {p : ℕ} [Fact p.Prime] [CharP k p]
    (X : SchemeOverField k) [Curve X] [Smooth X.hom] [Projective X.hom]
    [GeometricallyIrreducible X.hom] [ConnectedSpace X.left]
    (xbar : GeometricPoint X.left) (E : Type u) [Field E] [NumberField E]
    (ℓ ℓ' : HeightOneSpectrum (𝓞 E))
    (hℓ : ringChar (𝓞 E ⧸ ℓ.asIdeal) ≠ p)
    (hℓ' : ringChar (𝓞 E ⧸ ℓ'.asIdeal) ≠ p)
    (ρ : etaleFundamentalGroup X.left xbar →ₜ* SL(2, ℓ.adicCompletion E))
    (hρ : GeneralLinearGroup.IsAbsolutelyIrreducible
      (SpecialLinearGroup.toGL.comp ρ.toMonoidHom)),
    ∃ (E' : Type u) (_ : Field E') (_ : NumberField E') (ι : E →+* E')
      (μ : HeightOneSpectrum (𝓞 E'))
      (σ : ℓ'.adicCompletion E →+* μ.adicCompletion E')
      (τ : E' →+* ℓ.adicCompletion E)
      (ρ' : etaleFundamentalGroup X.left xbar →ₜ*
        SL(2, μ.adicCompletion E')),
      ι.Finite ∧ σ.Finite ∧
        σ.comp (FinitePlace.embedding ℓ') =
          (FinitePlace.embedding μ).comp ι ∧
        GeneralLinearGroup.IsAbsolutelyIrreducible
          (SpecialLinearGroup.toGL.comp ρ'.toMonoidHom) ∧
        IsFrobeniusCharpolyCompatible ι ℓ μ τ ρ ρ')

end AlgebraicGeometry.SchemeOverField
