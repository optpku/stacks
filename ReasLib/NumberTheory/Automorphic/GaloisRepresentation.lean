module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.Algebra.IntermediateField
public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.Frobenius
public import ReasLib.NumberTheory.Automorphic.UnramifiedHecke
public import ReasLib.RepresentationTheory.Matrix

@[expose] public section
noncomputable section
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
open CategoryTheory Matrix TopologicalSpace
universe u v
namespace AlgebraicGeometry.SchemeOverField
section
variable {k : Type u} [Field k]
variable {ℓ : ℕ} [Fact ℓ.Prime]
variable (X : SchemeOverField k)
variable (xbar : GeometricPoint X.left)

/-- The `U` eigenvalues have valuation exactly one in `PadicAlgCl ℓ`. -/
def Eigenform.u_mem_integer (f : Eigenform X (PadicAlgCl ℓ)) : Prop :=
  ∀ v : closedPoints X.left, (PadicAlgCl.valued ℓ).v (f.u v).val = 1

/-- The valuation-one condition unfolds to its pointwise form. -/
theorem Eigenform.u_mem_integer_iff (f : Eigenform X (PadicAlgCl ℓ)) :
    Eigenform.u_mem_integer X f ↔
      ∀ v : closedPoints X.left, (PadicAlgCl.valued ℓ).v (f.u v).val = 1 := Iff.rfl

/-- A finite coefficient field and an absolutely irreducible continuous representation
attached to an unramified eigenform, with its geometric-Frobenius identities. -/
theorem exists_galoisRepresentation_of_eigenform
    [Fintype k] {p : ℕ} [Fact p.Prime] [CharP k p]
    [Invertible (ringChar k : PadicAlgCl ℓ)]
    [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
    [ConnectedSpace X.left]
    (φ : UnramifiedCuspForm X (PadicAlgCl ℓ))
    (f : Eigenform X (PadicAlgCl ℓ)) (hφ : IsEigenform X φ f)
    (hu : Eigenform.u_mem_integer X f) :
    ∃ (E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ))
      (hE : FiniteDimensional ℚ_[ℓ] E)
      (ρ : etaleFundamentalGroup X.left xbar →ₜ* GL (Fin 2) E),
      GeneralLinearGroup.IsAbsolutelyIrreducible ρ.toMonoidHom ∧
        ∀ (v : closedPoints X.left)
          (ι : GeometricPoint.finiteFiber (geometricPointOverClosedPoint X v) ≅
            GeometricPoint.finiteFiber xbar),
          algebraMap E (PadicAlgCl ℓ)
              (Matrix.trace (ρ (etaleGeometricFrobenius X xbar v ι)).val) =
              f.t v ∧
            (f.u v).val =
              (residueCard X v : PadicAlgCl ℓ)⁻¹ *
                algebraMap E (PadicAlgCl ℓ)
                  (Matrix.det (ρ (etaleGeometricFrobenius X xbar v ι)).val) := sorry

end

namespace Eigenform

variable {k : Type u} [Field k] [Finite k]
variable {ℓ : ℕ} [Fact ℓ.Prime]
variable {X : SchemeOverField k} [LocallyOfFiniteType X.hom] [ConnectedSpace X.left]
variable {xbar : GeometricPoint X.left}
variable {E : Type v} [Field E] [Algebra E (PadicAlgCl ℓ)] [TopologicalSpace E]

/-- An eigenform `f` with values in `PadicAlgCl ℓ` is attached to a continuous
`GL (Fin 2)`-valued representation `ρ` when the Hecke eigenvalues match geometric
Frobenius: `t_v` equals the trace of `ρ (F_v)`, and `u_v` equals
`q_v⁻¹ * det (ρ (F_v))` after `algebraMap` to `PadicAlgCl ℓ`. -/
def IsAttachedTo (f : Eigenform X (PadicAlgCl ℓ))
    (ρ : etaleFundamentalGroup X.left xbar →ₜ* GL (Fin 2) E) : Prop :=
  ∀ (v : closedPoints X.left)
    (ι : GeometricPoint.finiteFiber (geometricPointOverClosedPoint X v) ≅
      GeometricPoint.finiteFiber xbar),
    algebraMap E (PadicAlgCl ℓ)
        (Matrix.trace (ρ (etaleGeometricFrobenius X xbar v ι)).val) =
      f.t v ∧
    (f.u v).val =
      (residueCard X v : PadicAlgCl ℓ)⁻¹ *
        algebraMap E (PadicAlgCl ℓ)
          (Matrix.det (ρ (etaleGeometricFrobenius X xbar v ι)).val)

/-- Unfolding of attachment as matching of traces and determinants of geometric
Frobenius after `algebraMap` to `PadicAlgCl ℓ`. -/
theorem isAttachedTo_iff (f : Eigenform X (PadicAlgCl ℓ))
    (ρ : etaleFundamentalGroup X.left xbar →ₜ* GL (Fin 2) E) :
    f.IsAttachedTo ρ ↔
      ∀ (v : closedPoints X.left)
        (ι : GeometricPoint.finiteFiber (geometricPointOverClosedPoint X v) ≅
          GeometricPoint.finiteFiber xbar),
        algebraMap E (PadicAlgCl ℓ)
            (Matrix.trace (ρ (etaleGeometricFrobenius X xbar v ι)).val) =
          f.t v ∧
        (f.u v).val =
          (residueCard X v : PadicAlgCl ℓ)⁻¹ *
            algebraMap E (PadicAlgCl ℓ)
              (Matrix.det (ρ (etaleGeometricFrobenius X xbar v ι)).val) := sorry

variable {f : Eigenform X (PadicAlgCl ℓ)}
variable {ρ : etaleFundamentalGroup X.left xbar →ₜ* GL (Fin 2) E}

/-- Attached eigenforms recover Hecke eigenvalues `t_v` as traces of `ρ (F_v)`. -/
theorem isAttachedTo_t (hf : f.IsAttachedTo ρ) (v : closedPoints X.left)
    (ι : GeometricPoint.finiteFiber (geometricPointOverClosedPoint X v) ≅
      GeometricPoint.finiteFiber xbar) :
    f.t v =
      algebraMap E (PadicAlgCl ℓ)
        (Matrix.trace (ρ (etaleGeometricFrobenius X xbar v ι)).val) := sorry

/-- Attached eigenforms recover Hecke eigenvalues `u_v` as
`q_v⁻¹ * det (ρ (F_v))` after `algebraMap` to `PadicAlgCl ℓ`. -/
theorem isAttachedTo_u (hf : f.IsAttachedTo ρ) (v : closedPoints X.left)
    (ι : GeometricPoint.finiteFiber (geometricPointOverClosedPoint X v) ≅
      GeometricPoint.finiteFiber xbar) :
    (f.u v).val =
      (residueCard X v : PadicAlgCl ℓ)⁻¹ *
        algebraMap E (PadicAlgCl ℓ)
          (Matrix.det (ρ (etaleGeometricFrobenius X xbar v ι)).val) := sorry

end Eigenform

/-- Every continuous absolutely irreducible two-dimensional representation of the étale
fundamental group of a geometrically irreducible smooth projective curve over a finite field,
with coefficients in a finite extension of `ℚ_[ℓ]`, admits an unramified cusp eigenform over
`PadicAlgCl ℓ` whose Hecke eigenvalues are the geometric-Frobenius traces and
residue-cardinality-normalized determinants. -/
theorem exists_eigenform_of_galoisRepresentation
    {k : Type u} [Field k] [Fintype k] {p ℓ : ℕ} [Fact p.Prime] [Fact ℓ.Prime] [CharP k p]
    [Invertible (ringChar k : PadicAlgCl ℓ)]
    (X : SchemeOverField k)
    [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
    [ConnectedSpace X.left]
    (xbar : GeometricPoint X.left)
    (E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) [FiniteDimensional ℚ_[ℓ] E]
    (ρ : etaleFundamentalGroup X.left xbar →ₜ* GL (Fin 2) E)
    (hirr : GeneralLinearGroup.IsAbsolutelyIrreducible ρ.toMonoidHom) :
    ∃ (φ : UnramifiedCuspForm X (PadicAlgCl ℓ)) (f : Eigenform X (PadicAlgCl ℓ)),
      IsEigenform X φ f ∧ f.IsAttachedTo ρ := sorry
end AlgebraicGeometry.SchemeOverField
