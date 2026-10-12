/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Instances.Matrix
public import stacks_project.Chap64.Theorem_64_31_2_Eigenform
public import stacks_project.Chap64.Theorem_64_31_2_Frobenius

/-!
# Attachment of unramified GL₂ eigenforms to Galois representations

This leaf owns the matching relation between Hecke eigenvalues of an unramified
`GL (Fin 2)` eigenform and traces/determinants of geometric Frobenius.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
open CategoryTheory Matrix

universe u v

namespace AlgebraicGeometry.SchemeOverField

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
    (ι : standardFiniteEtaleFiber (geometricPointOverClosedPoint X v) ≅
      standardFiniteEtaleFiber xbar),
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
        (ι : standardFiniteEtaleFiber (geometricPointOverClosedPoint X v) ≅
          standardFiniteEtaleFiber xbar),
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
    (ι : standardFiniteEtaleFiber (geometricPointOverClosedPoint X v) ≅
      standardFiniteEtaleFiber xbar) :
    f.t v =
      algebraMap E (PadicAlgCl ℓ)
        (Matrix.trace (ρ (etaleGeometricFrobenius X xbar v ι)).val) := sorry

/-- Attached eigenforms recover Hecke eigenvalues `u_v` as
`q_v⁻¹ * det (ρ (F_v))` after `algebraMap` to `PadicAlgCl ℓ`. -/
theorem isAttachedTo_u (hf : f.IsAttachedTo ρ) (v : closedPoints X.left)
    (ι : standardFiniteEtaleFiber (geometricPointOverClosedPoint X v) ≅
      standardFiniteEtaleFiber xbar) :
    (f.u v).val =
      (residueCard X v : PadicAlgCl ℓ)⁻¹ *
        algebraMap E (PadicAlgCl ℓ)
          (Matrix.det (ρ (etaleGeometricFrobenius X xbar v ι)).val) := sorry

end Eigenform

end AlgebraicGeometry.SchemeOverField
