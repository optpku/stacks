/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Group.Matrix
public import Mathlib.Topology.Algebra.IntermediateField
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Instances.Matrix
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import stacks_project.Chap64.Theorem_64_31_10_GLRep
public import stacks_project.Chap64.Theorem_64_31_2_Eigenform
public import stacks_project.Chap64.Theorem_64_31_2_Frobenius
public import stacks_project.Chap64.Theorem_64_31_2_Hecke

/-!
# Galois representations attached to unramified GL₂ eigenforms

Drinfeld's existence theorem: an unramified `GL (Fin 2)` eigenform with
values in `PadicAlgCl ℓ` and `U`-eigenvalues in the units of the valuation
ring yields a continuous absolutely irreducible representation of
`π₁(X)` matching Hecke eigenvalues on geometric Frobenius.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
open CategoryTheory Matrix TopologicalSpace

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]
variable {ℓ : ℕ} [Fact ℓ.Prime]
variable (X : SchemeOverField k)
variable (xbar : GeometricPoint X.left)

/-- The `U`-eigenvalues of `f` lie in the unit group of the valuation ring of
`PadicAlgCl ℓ`, equivalently `(PadicAlgCl.valued ℓ).v (f.u v).val = 1`. -/
def Eigenform.u_mem_integer (f : Eigenform X (PadicAlgCl ℓ)) : Prop :=
  ∀ v : closedPoints X.left, (PadicAlgCl.valued ℓ).v (f.u v).val = 1

/-- Unfolding of `u_v ∈ Z̄_ℓ^*` as valuation exactly `1`. -/
theorem Eigenform.u_mem_integer_iff (f : Eigenform X (PadicAlgCl ℓ)) :
    Eigenform.u_mem_integer X f ↔
      ∀ v : closedPoints X.left, (PadicAlgCl.valued ℓ).v (f.u v).val = 1 := sorry

/-- Theorem 64.31.2. Given an eigenform `f` with values in `PadicAlgCl ℓ` and
eigenvalues `u_v` in the unit group of the valuation ring of `PadicAlgCl ℓ`,
there exists a continuous absolutely irreducible representation
`ρ : π₁(X, xbar) →ₜ* GL (Fin 2) E` on a finite extension `E` of `ℚ_[ℓ]`
contained in `PadicAlgCl ℓ` such that `t_v = Matrix.trace (ρ F_v)` and
`u_v = (residueCard v)⁻¹ * Matrix.det (ρ F_v)` at every closed point `v`. -/
@[stacks 03VT]
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
          (ι : standardFiniteEtaleFiber (geometricPointOverClosedPoint X v) ≅
            standardFiniteEtaleFiber xbar),
          algebraMap E (PadicAlgCl ℓ)
              (Matrix.trace (ρ (etaleGeometricFrobenius X xbar v ι)).val) =
              f.t v ∧
            (f.u v).val =
              (residueCard X v : PadicAlgCl ℓ)⁻¹ *
                algebraMap E (PadicAlgCl ℓ)
                  (Matrix.det (ρ (etaleGeometricFrobenius X xbar v ι)).val) := sorry

end AlgebraicGeometry.SchemeOverField
