/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.NumberTheory.Automorphic.GaloisRepresentation

/-!
# Galois representations attached to unramified GL₂ eigenforms

The source-facing bridge for the Drinfeld existence theorem.
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

/- Theorem 64.31.2. -/
@[stacks 03VT]
#check (AlgebraicGeometry.SchemeOverField.exists_galoisRepresentation_of_eigenform :
    ∀ (X : SchemeOverField k) (xbar : GeometricPoint X.left), ∀ [Fintype k]
    {p : ℕ} [Fact p.Prime] [CharP k p]
    [Invertible (ringChar k : PadicAlgCl ℓ)]
    [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
    [ConnectedSpace X.left]
    (φ : UnramifiedCuspForm X (PadicAlgCl ℓ))
    (f : Eigenform X (PadicAlgCl ℓ)) (hφ : IsEigenform X φ f)
    (hu : Eigenform.u_mem_integer X f),
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
                  (Matrix.det (ρ (etaleGeometricFrobenius X xbar v ι)).val))

end AlgebraicGeometry.SchemeOverField
