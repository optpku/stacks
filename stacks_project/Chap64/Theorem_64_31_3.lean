/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.NumberTheory.Automorphic.GaloisRepresentation
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
open Matrix

universe u

/- Theorem 64.31.3. Let `k` be a finite field of characteristic `p`, and let `X`
be a geometrically irreducible smooth projective curve over `k`. Suppose
`ℚ_[ℓ] ⊂ E` is a finite extension inside `PadicAlgCl ℓ`, and
`ρ : π₁(X, xbar) →ₜ* GL (Fin 2) E` is continuous and absolutely irreducible.
Then there exists an unramified cusp form `φ` with values in `PadicAlgCl ℓ`
which is an eigenform in the sense of `IsEigenform`, with
Hecke eigenvalues `t_v`, `u_v` satisfying `t_v = Tr(ρ(F_v))` and
`u_v = q_v⁻¹ det(ρ(F_v))` at every closed point `v`, recorded by
`Eigenform.IsAttachedTo`. -/
@[stacks 03VU] #check
  (AlgebraicGeometry.SchemeOverField.exists_eigenform_of_galoisRepresentation :
    ∀ {k : Type u} [Field k] [Fintype k] {p ℓ : ℕ} [Fact p.Prime] [Fact ℓ.Prime] [CharP k p]
    [Invertible (ringChar k : PadicAlgCl ℓ)]
    (X : SchemeOverField k)
    [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
    [ConnectedSpace X.left]
    (xbar : GeometricPoint X.left)
    (E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) [FiniteDimensional ℚ_[ℓ] E]
    (ρ : etaleFundamentalGroup X.left xbar →ₜ* GL (Fin 2) E)
    (hirr : GeneralLinearGroup.IsAbsolutelyIrreducible ρ.toMonoidHom),
    ∃ (φ : UnramifiedCuspForm X (PadicAlgCl ℓ)) (f : Eigenform X (PadicAlgCl ℓ)),
      IsEigenform X φ f ∧ f.IsAttachedTo ρ)
