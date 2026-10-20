module

public import Mathlib.Algebra.CharP.Basic
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Matrix
public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.Frobenius
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import ReasLib.RepresentationTheory.Matrix

/-!
# Frobenius characteristic polynomials of SL(2) representations

Characteristic polynomials of geometric Frobenius under a continuous
`SL(2)`-valued representation of an étale fundamental group, and compatibility
of two such representations at places of number fields.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
open CategoryTheory IsDedekindDomain Matrix NumberField
open scoped MatrixGroups NumberField

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k] [Finite k]
variable {E : Type u} [Field E] [NumberField E]
variable {X : SchemeOverField k} [ConnectedSpace X.left] [LocallyOfFiniteType X.hom]
variable {xbar : GeometricPoint X.left}

/-- Characteristic polynomial of geometric Frobenius `F_v` under a continuous
`SL(2)`-valued representation of `etaleFundamentalGroup X.left xbar`. -/
def frobeniusCharpoly {ℓ : HeightOneSpectrum (𝓞 E)}
    (ρ : etaleFundamentalGroup X.left xbar →ₜ* SL(2, ℓ.adicCompletion E))
    (v : closedPoints X.left)
    (ι : GeometricPoint.finiteFiber (geometricPointOverClosedPoint X v) ≅
      GeometricPoint.finiteFiber xbar) :
    Polynomial (ℓ.adicCompletion E) :=
  Matrix.charpoly (SpecialLinearGroup.toGL (ρ (etaleGeometricFrobenius X xbar v ι))).val

/-- Unfolding of `frobeniusCharpoly` as the matrix characteristic polynomial of
`SpecialLinearGroup.toGL` applied to geometric Frobenius. -/
theorem frobeniusCharpoly_apply {ℓ : HeightOneSpectrum (𝓞 E)}
    (ρ : etaleFundamentalGroup X.left xbar →ₜ* SL(2, ℓ.adicCompletion E))
    (v : closedPoints X.left)
    (ι : GeometricPoint.finiteFiber (geometricPointOverClosedPoint X v) ≅
      GeometricPoint.finiteFiber xbar) :
    frobeniusCharpoly ρ v ι =
      Matrix.charpoly (SpecialLinearGroup.toGL
        (ρ (etaleGeometricFrobenius X xbar v ι))).val := sorry

/-- Two continuous `SL(2)` representations, with coefficients in the adic
completions of number fields `E` and `E'` at places `ℓ` and `μ`, are Frobenius
charpoly compatible along `ι : E →+* E'` and `τ : E' →+* ℓ.adicCompletion E`
when `τ` extends `FinitePlace.embedding ℓ` along `ι`, and every geometric
Frobenius has the same characteristic polynomial, realized by a polynomial
over `E'` mapped along `τ` and along `FinitePlace.embedding μ`. -/
def IsFrobeniusCharpolyCompatible {E' : Type u} [Field E'] [NumberField E']
    (ι : E →+* E') (ℓ : HeightOneSpectrum (𝓞 E)) (μ : HeightOneSpectrum (𝓞 E'))
    (τ : E' →+* ℓ.adicCompletion E)
    (ρ : etaleFundamentalGroup X.left xbar →ₜ* SL(2, ℓ.adicCompletion E))
    (ρ' : etaleFundamentalGroup X.left xbar →ₜ* SL(2, μ.adicCompletion E')) :
    Prop :=
  τ.comp ι = FinitePlace.embedding ℓ ∧
    ∀ (v : closedPoints X.left)
      (ιFrob : GeometricPoint.finiteFiber (geometricPointOverClosedPoint X v) ≅
        GeometricPoint.finiteFiber xbar),
      ∃ p : Polynomial E',
        p.map τ = frobeniusCharpoly ρ v ιFrob ∧
          p.map (FinitePlace.embedding μ) = frobeniusCharpoly ρ' v ιFrob

/-- Unfolding of Frobenius characteristic-polynomial compatibility as an
embedding of `E'` into `ℓ.adicCompletion E` extending `FinitePlace.embedding ℓ`,
together with matching after mapping a polynomial over `E'` along that
embedding and along `FinitePlace.embedding μ`. -/
theorem isFrobeniusCharpolyCompatible_iff {E' : Type u} [Field E'] [NumberField E']
    (ι : E →+* E') (ℓ : HeightOneSpectrum (𝓞 E)) (μ : HeightOneSpectrum (𝓞 E'))
    (τ : E' →+* ℓ.adicCompletion E)
    (ρ : etaleFundamentalGroup X.left xbar →ₜ* SL(2, ℓ.adicCompletion E))
    (ρ' : etaleFundamentalGroup X.left xbar →ₜ* SL(2, μ.adicCompletion E')) :
    IsFrobeniusCharpolyCompatible ι ℓ μ τ ρ ρ' ↔
      τ.comp ι = FinitePlace.embedding ℓ ∧
        ∀ (v : closedPoints X.left)
          (ιFrob : GeometricPoint.finiteFiber (geometricPointOverClosedPoint X v) ≅
            GeometricPoint.finiteFiber xbar),
          ∃ p : Polynomial E',
            p.map τ = frobeniusCharpoly ρ v ιFrob ∧
              p.map (FinitePlace.embedding μ) =
                frobeniusCharpoly ρ' v ιFrob := sorry

/-- Let `X` be a geometrically irreducible smooth projective curve over a finite
field of characteristic `p`. Let `E` be a number field, and let
`ρ : etaleFundamentalGroup X.left xbar →ₜ* SL(2, ℓ.adicCompletion E)` be
absolutely irreducible and continuous, where `ℓ` is a finite place of `E` not
lying above `p`. Then for any second finite place `ℓ'` of `E` not lying above
`p` there exists a finite extension of `ℓ'.adicCompletion E` carrying an
absolutely irreducible continuous representation
`ρ' : etaleFundamentalGroup X.left xbar →ₜ* SL(2, μ.adicCompletion E')`
compatible with `ρ` in the sense that the characteristic polynomials of all
geometric Frobenii are the same. -/
theorem exists_compatible_specialLinearRepresentation
    {k : Type u} [Field k] [Finite k] {p : ℕ} [Fact p.Prime] [CharP k p]
    (X : SchemeOverField k) [Curve X] [Smooth X.hom] [Projective X.hom]
    [GeometricallyIrreducible X.hom] [ConnectedSpace X.left]
    (xbar : GeometricPoint X.left) (E : Type u) [Field E] [NumberField E]
    (ℓ ℓ' : HeightOneSpectrum (𝓞 E))
    (hℓ : ringChar (𝓞 E ⧸ ℓ.asIdeal) ≠ p)
    (hℓ' : ringChar (𝓞 E ⧸ ℓ'.asIdeal) ≠ p)
    (ρ : etaleFundamentalGroup X.left xbar →ₜ* SL(2, ℓ.adicCompletion E))
    (hρ : GeneralLinearGroup.IsAbsolutelyIrreducible
      (SpecialLinearGroup.toGL.comp ρ.toMonoidHom)) :
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
        IsFrobeniusCharpolyCompatible ι ℓ μ τ ρ ρ' := sorry

end AlgebraicGeometry.SchemeOverField
