/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.CharP.Basic
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Algebra.IntermediateField
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import stacks_project.Chap64.Theorem_64_31_10_GLRep
public import stacks_project.Chap64.Theorem_64_31_2_Hecke
public import stacks_project.Chap64.Theorem_64_31_3_Attachment

/-!
# Drinfeld converse: eigenforms from Galois representations

An absolutely irreducible continuous `GL (Fin 2)` representation of `π₁(X)`
on a finite extension of `ℚ_[ℓ]` yields an unramified cusp form over
`PadicAlgCl ℓ` which is a Hecke eigenform matching traces and normalized
determinants of geometric Frobenius.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
open Matrix

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- Theorem 64.31.3. Let `k` be a finite field of characteristic `p`, and let `X`
be a geometrically irreducible smooth projective curve over `k`. Suppose
`ℚ_[ℓ] ⊂ E` is a finite extension inside `PadicAlgCl ℓ`, and
`ρ : π₁(X, xbar) →ₜ* GL (Fin 2) E` is continuous and absolutely irreducible.
Then there exists an unramified cusp form `φ` with values in `PadicAlgCl ℓ`
which is an eigenform in the sense of `IsEigenform`, with
Hecke eigenvalues `t_v`, `u_v` satisfying `t_v = Tr(ρ(F_v))` and
`u_v = q_v⁻¹ det(ρ(F_v))` at every closed point `v`, recorded by
`Eigenform.IsAttachedTo`. -/
@[stacks 03VU]
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
