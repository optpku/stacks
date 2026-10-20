/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Deformation

/-!
# Fixed-determinant finiteness and unrestricted flatness

The uploaded source is preserved. The local correction recorded here restricts
only the finite-over-`ℤ_[ℓ]` assertion to universal deformations with the same
arbitrary continuous determinant lift in every test algebra. The fixed-
determinant flatness companion is retained, while unrestricted flatness and
characteristic-zero lifting remain unrestricted.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
open Deformation IsLocalRing Matrix Matrix.GeneralLinearGroup

universe u

namespace AlgebraicGeometry.SchemeOverField

/- Theorem 64.31.10 (1). A universal deformation with a fixed continuous determinant is finite over `ℤ_[ℓ]`. -/
@[stacks 03W1] #check (AlgebraicGeometry.SchemeOverField.fixedDeterminantUniversalDeformationRing_moduleFinite :
  ∀ {k : Type u} [Field k] [Finite k] {p ℓ n : ℕ} [Fact p.Prime] [Fact ℓ.Prime] [CharP k p]
    (hℓp : ℓ ≠ p) (hℓn : ¬ ℓ ∣ n) (X : SchemeOverField k)
    [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
    [ConnectedSpace (geometricBaseChange X)]
    (xbar : GeometricPoint (geometricBaseChange X))
    (hconj : ∀ r : ℕ, deJongConjectureAt X xbar ℓ r)
    (ρ₀ : ContinuousMonoidHom
      (etaleFundamentalGroup X.left (arithmeticPoint X xbar)) (GL (Fin n) (ZMod ℓ)))
    (hirr : IsAbsolutelyIrreducible
      (ρ₀.toMonoidHom.comp (geometricToArithmetic X xbar).hom.toMonoidHom))
    {R : Type u} [CommRing R] [IsLocalRing R] [Algebra ℤ_[ℓ] R]
    [TopologicalSpace R] [IsTopologicalRing R]
    [Fact (IsAdic (maximalIdeal R))] [IsAdicComplete (maximalIdeal R) R]
    [IsLAdicAlgebra ℓ R]
    (δ : ContinuousMonoidHom
      (etaleFundamentalGroup X.left (arithmeticPoint X xbar)) ℤ_[ℓ]ˣ)
    (ρuniv : ContinuousMonoidHom
      (etaleFundamentalGroup X.left (arithmeticPoint X xbar)) (GL (Fin n) R))
    (huniv : IsUniversalFixedDeterminantDeformation ρ₀ δ ρuniv),
    Module.Finite ℤ_[ℓ] R)

/- A universal deformation with a fixed continuous determinant is flat over `ℤ_[ℓ]`. -/
@[stacks 03W1] #check (AlgebraicGeometry.SchemeOverField.fixedDeterminantUniversalDeformationRing_moduleFlat :
  ∀ {k : Type u} [Field k] [Finite k] {p ℓ n : ℕ} [Fact p.Prime] [Fact ℓ.Prime] [CharP k p]
    (hℓp : ℓ ≠ p) (hℓn : ¬ ℓ ∣ n) (X : SchemeOverField k)
    [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
    [ConnectedSpace (geometricBaseChange X)]
    (xbar : GeometricPoint (geometricBaseChange X))
    (hconj : ∀ r : ℕ, deJongConjectureAt X xbar ℓ r)
    (ρ₀ : ContinuousMonoidHom
      (etaleFundamentalGroup X.left (arithmeticPoint X xbar)) (GL (Fin n) (ZMod ℓ)))
    (hirr : IsAbsolutelyIrreducible
      (ρ₀.toMonoidHom.comp (geometricToArithmetic X xbar).hom.toMonoidHom))
    {R : Type u} [CommRing R] [IsLocalRing R] [Algebra ℤ_[ℓ] R]
    [TopologicalSpace R] [IsTopologicalRing R]
    [Fact (IsAdic (maximalIdeal R))] [IsAdicComplete (maximalIdeal R) R]
    [IsLAdicAlgebra ℓ R]
    (δ : ContinuousMonoidHom
      (etaleFundamentalGroup X.left (arithmeticPoint X xbar)) ℤ_[ℓ]ˣ)
    (ρuniv : ContinuousMonoidHom
      (etaleFundamentalGroup X.left (arithmeticPoint X xbar)) (GL (Fin n) R))
    (huniv : IsUniversalFixedDeterminantDeformation ρ₀ δ ρuniv),
    Module.Flat ℤ_[ℓ] R)

/- Theorem 64.31.10 (2). An unrestricted universal deformation is flat over `ℤ_[ℓ]`. -/
@[stacks 03W1] #check (AlgebraicGeometry.SchemeOverField.universalDeformationRing_moduleFlat :
  ∀ {k : Type u} [Field k] [Finite k] {p ℓ n : ℕ} [Fact p.Prime] [Fact ℓ.Prime] [CharP k p]
    (hℓp : ℓ ≠ p) (hℓn : ¬ ℓ ∣ n) (X : SchemeOverField k)
    [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
    [ConnectedSpace (geometricBaseChange X)]
    (xbar : GeometricPoint (geometricBaseChange X))
    (hconj : ∀ r : ℕ, deJongConjectureAt X xbar ℓ r)
    (ρ₀ : ContinuousMonoidHom
      (etaleFundamentalGroup X.left (arithmeticPoint X xbar)) (GL (Fin n) (ZMod ℓ)))
    (hirr : IsAbsolutelyIrreducible
      (ρ₀.toMonoidHom.comp (geometricToArithmetic X xbar).hom.toMonoidHom))
    {R : Type u} [CommRing R] [IsLocalRing R] [Algebra ℤ_[ℓ] R]
    [TopologicalSpace R] [IsTopologicalRing R]
    [Fact (IsAdic (maximalIdeal R))] [IsAdicComplete (maximalIdeal R) R]
    [IsLAdicAlgebra ℓ R]
    (ρuniv : ContinuousMonoidHom
      (etaleFundamentalGroup X.left (arithmeticPoint X xbar)) (GL (Fin n) R))
    (huniv : IsUniversalDeformation ρ₀ ρuniv),
    Module.Flat ℤ_[ℓ] R)

/- An unrestricted universal deformation admits a coefficient-compatible continuous lift to `AlgebraicClosure ℚ_[ℓ]`. -/
@[stacks 03W1] #check (AlgebraicGeometry.SchemeOverField.exists_qlBarLift :
  ∀ {k : Type u} [Field k] [Finite k] {p ℓ n : ℕ} [Fact p.Prime] [Fact ℓ.Prime] [CharP k p]
    (hℓp : ℓ ≠ p) (hℓn : ¬ ℓ ∣ n) (X : SchemeOverField k)
    [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
    [ConnectedSpace (geometricBaseChange X)]
    (xbar : GeometricPoint (geometricBaseChange X))
    (hconj : ∀ r : ℕ, deJongConjectureAt X xbar ℓ r)
    (ρ₀ : ContinuousMonoidHom
      (etaleFundamentalGroup X.left (arithmeticPoint X xbar)) (GL (Fin n) (ZMod ℓ)))
    (hirr : IsAbsolutelyIrreducible
      (ρ₀.toMonoidHom.comp (geometricToArithmetic X xbar).hom.toMonoidHom))
    {R : Type u} [CommRing R] [IsLocalRing R] [Algebra ℤ_[ℓ] R]
    [TopologicalSpace R] [IsTopologicalRing R]
    [Fact (IsAdic (maximalIdeal R))] [IsAdicComplete (maximalIdeal R) R]
    [IsLAdicAlgebra ℓ R]
    (ρuniv : ContinuousMonoidHom
      (etaleFundamentalGroup X.left (arithmeticPoint X xbar)) (GL (Fin n) R))
    (huniv : IsUniversalDeformation ρ₀ ρuniv),
    ∃ (ρ : ContinuousMonoidHom
        (etaleFundamentalGroup X.left (arithmeticPoint X xbar))
        (GL (Fin n) (AlgebraicClosure ℚ_[ℓ])))
      (ψ : R →+* AlgebraicClosure ℚ_[ℓ]),
      ρ.toMonoidHom = (GeneralLinearGroup.map ψ).comp ρuniv.toMonoidHom ∧
        ψ.comp (algebraMap ℤ_[ℓ] R) =
          (algebraMap ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ])).comp
            (algebraMap ℤ_[ℓ] ℚ_[ℓ]))

end AlgebraicGeometry.SchemeOverField
