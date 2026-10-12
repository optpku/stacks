/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Matrix
public import stacks_project.Chap64.Theorem_64_31_2_Frobenius

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
    (ι : standardFiniteEtaleFiber (geometricPointOverClosedPoint X v) ≅
      standardFiniteEtaleFiber xbar) :
    Polynomial (ℓ.adicCompletion E) :=
  Matrix.charpoly (SpecialLinearGroup.toGL (ρ (etaleGeometricFrobenius X xbar v ι))).val

/-- Unfolding of `frobeniusCharpoly` as the matrix characteristic polynomial of
`SpecialLinearGroup.toGL` applied to geometric Frobenius. -/
theorem frobeniusCharpoly_apply {ℓ : HeightOneSpectrum (𝓞 E)}
    (ρ : etaleFundamentalGroup X.left xbar →ₜ* SL(2, ℓ.adicCompletion E))
    (v : closedPoints X.left)
    (ι : standardFiniteEtaleFiber (geometricPointOverClosedPoint X v) ≅
      standardFiniteEtaleFiber xbar) :
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
      (ιFrob : standardFiniteEtaleFiber (geometricPointOverClosedPoint X v) ≅
        standardFiniteEtaleFiber xbar),
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
          (ιFrob : standardFiniteEtaleFiber (geometricPointOverClosedPoint X v) ≅
            standardFiniteEtaleFiber xbar),
          ∃ p : Polynomial E',
            p.map τ = frobeniusCharpoly ρ v ιFrob ∧
              p.map (FinitePlace.embedding μ) =
                frobeniusCharpoly ρ' v ιFrob := sorry

end AlgebraicGeometry.SchemeOverField
