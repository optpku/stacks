module

public import Mathlib.Algebra.CharP.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.Flat.Basic
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.DeJong
public import ReasLib.RepresentationTheory.Deformation.FixedDeterminant
public import ReasLib.RepresentationTheory.Matrix

@[expose] public section

noncomputable section

open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
open Deformation IsLocalRing Matrix Matrix.GeneralLinearGroup

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- Under de Jong's conjecture and geometric absolute irreducibility, a universal deformation with a fixed continuous determinant is finite over `ℤ_[ℓ]`. -/
theorem fixedDeterminantUniversalDeformationRing_moduleFinite
    {k : Type u} [Field k] [Finite k] {p ℓ n : ℕ} [Fact p.Prime] [Fact ℓ.Prime] [CharP k p]
    (hℓp : ℓ ≠ p) (hℓn : ¬ ℓ ∣ n) (X : SchemeOverField k)
    [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
    [ConnectedSpace (geometricBaseChange X)]
    (xbar : GeometricPoint (geometricBaseChange X))
    (hconj : ∀ r : ℕ, deJongConjectureAt X xbar ℓ r)
    (ρ₀ : ContinuousMonoidHom (etaleFundamentalGroup X.left (arithmeticPoint X xbar))
      (GL (Fin n) (ZMod ℓ)))
    (hirr : IsAbsolutelyIrreducible
      (ρ₀.toMonoidHom.comp (geometricToArithmetic X xbar).hom.toMonoidHom))
    {R : Type u} [CommRing R] [IsLocalRing R] [Algebra ℤ_[ℓ] R]
    [TopologicalSpace R] [IsTopologicalRing R]
    [Fact (IsAdic (maximalIdeal R))]
    [IsAdicComplete (maximalIdeal R) R] [IsLAdicAlgebra ℓ R]
    (δ : ContinuousMonoidHom (etaleFundamentalGroup X.left (arithmeticPoint X xbar))
      ℤ_[ℓ]ˣ)
    (ρuniv : ContinuousMonoidHom (etaleFundamentalGroup X.left (arithmeticPoint X xbar))
      (GL (Fin n) R))
    (huniv : IsUniversalFixedDeterminantDeformation ρ₀ δ ρuniv) :
    Module.Finite ℤ_[ℓ] R := sorry

/-- For a smooth projective geometrically irreducible curve over a finite field of
characteristic `p`, assume de Jong's conjecture in every rank at the prime `ℓ` and
geometric base point `xbar`, with `ℓ ≠ p` and `ℓ ∤ n`. If a continuous rank-`n` residual
representation is geometrically absolutely irreducible, its complete local universal
deformation ring with an arbitrary fixed continuous determinant lift is flat over `ℤ_[ℓ]`.
The determinant lifts the residual determinant and is fixed in every test deformation. -/
theorem fixedDeterminantUniversalDeformationRing_moduleFlat
    {k : Type u} [Field k] [Finite k] {p ℓ n : ℕ} [Fact p.Prime] [Fact ℓ.Prime] [CharP k p]
    (hℓp : ℓ ≠ p) (hℓn : ¬ ℓ ∣ n) (X : SchemeOverField k)
    [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
    [ConnectedSpace (geometricBaseChange X)]
    (xbar : GeometricPoint (geometricBaseChange X))
    (hconj : ∀ r : ℕ, deJongConjectureAt X xbar ℓ r)
    (ρ₀ : ContinuousMonoidHom (etaleFundamentalGroup X.left (arithmeticPoint X xbar))
      (GL (Fin n) (ZMod ℓ)))
    (hirr : IsAbsolutelyIrreducible
      (ρ₀.toMonoidHom.comp (geometricToArithmetic X xbar).hom.toMonoidHom))
    {R : Type u} [CommRing R] [IsLocalRing R] [Algebra ℤ_[ℓ] R]
    [TopologicalSpace R] [IsTopologicalRing R]
    [Fact (IsAdic (maximalIdeal R))]
    [IsAdicComplete (maximalIdeal R) R] [IsLAdicAlgebra ℓ R]
    (δ : ContinuousMonoidHom (etaleFundamentalGroup X.left (arithmeticPoint X xbar))
      ℤ_[ℓ]ˣ)
    (ρuniv : ContinuousMonoidHom (etaleFundamentalGroup X.left (arithmeticPoint X xbar))
      (GL (Fin n) R))
    (huniv : IsUniversalFixedDeterminantDeformation ρ₀ δ ρuniv) :
    Module.Flat ℤ_[ℓ] R := sorry

/-- Under de Jong's conjecture and geometric absolute irreducibility, an unrestricted universal deformation is flat over `ℤ_[ℓ]`. -/
theorem universalDeformationRing_moduleFlat
    {k : Type u} [Field k] [Finite k] {p ℓ n : ℕ} [Fact p.Prime] [Fact ℓ.Prime] [CharP k p]
    (hℓp : ℓ ≠ p) (hℓn : ¬ ℓ ∣ n) (X : SchemeOverField k)
    [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
    [ConnectedSpace (geometricBaseChange X)]
    (xbar : GeometricPoint (geometricBaseChange X))
    (hconj : ∀ r : ℕ, deJongConjectureAt X xbar ℓ r)
    (ρ₀ : ContinuousMonoidHom (etaleFundamentalGroup X.left (arithmeticPoint X xbar))
      (GL (Fin n) (ZMod ℓ)))
    (hirr : IsAbsolutelyIrreducible
      (ρ₀.toMonoidHom.comp (geometricToArithmetic X xbar).hom.toMonoidHom))
    {R : Type u} [CommRing R] [IsLocalRing R] [Algebra ℤ_[ℓ] R]
    [TopologicalSpace R] [IsTopologicalRing R]
    [Fact (IsAdic (maximalIdeal R))]
    [IsAdicComplete (maximalIdeal R) R] [IsLAdicAlgebra ℓ R]
    (ρuniv : ContinuousMonoidHom (etaleFundamentalGroup X.left (arithmeticPoint X xbar))
      (GL (Fin n) R))
    (huniv : IsUniversalDeformation ρ₀ ρuniv) :
    Module.Flat ℤ_[ℓ] R := sorry

/-- For a smooth projective geometrically irreducible curve over a finite field of
characteristic `p`, assume de Jong's conjecture in every rank at the prime `ℓ` and
geometric base point `xbar`, with `ℓ ≠ p` and `ℓ ∤ n`. If a continuous rank-`n` residual
representation is geometrically absolutely irreducible, its unrestricted complete local
universal deformation admits a continuous representation over `AlgebraicClosure ℚ_[ℓ]`.
This representation is the specialization of `ρuniv` along a ring map from `R` whose
restriction to `ℤ_[ℓ]` is the canonical coefficient map through `ℚ_[ℓ]`. -/
theorem exists_qlBarLift
    {k : Type u} [Field k] [Finite k] {p ℓ n : ℕ} [Fact p.Prime] [Fact ℓ.Prime] [CharP k p]
    (hℓp : ℓ ≠ p) (hℓn : ¬ ℓ ∣ n) (X : SchemeOverField k)
    [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
    [ConnectedSpace (geometricBaseChange X)]
    (xbar : GeometricPoint (geometricBaseChange X))
    (hconj : ∀ r : ℕ, deJongConjectureAt X xbar ℓ r)
    (ρ₀ : ContinuousMonoidHom (etaleFundamentalGroup X.left (arithmeticPoint X xbar))
      (GL (Fin n) (ZMod ℓ)))
    (hirr : IsAbsolutelyIrreducible
      (ρ₀.toMonoidHom.comp (geometricToArithmetic X xbar).hom.toMonoidHom))
    {R : Type u} [CommRing R] [IsLocalRing R] [Algebra ℤ_[ℓ] R]
    [TopologicalSpace R] [IsTopologicalRing R]
    [Fact (IsAdic (maximalIdeal R))]
    [IsAdicComplete (maximalIdeal R) R] [IsLAdicAlgebra ℓ R]
    (ρuniv : ContinuousMonoidHom (etaleFundamentalGroup X.left (arithmeticPoint X xbar))
      (GL (Fin n) R))
    (huniv : IsUniversalDeformation ρ₀ ρuniv) :
    ∃ (ρ : ContinuousMonoidHom (etaleFundamentalGroup X.left (arithmeticPoint X xbar))
        (GL (Fin n) (AlgebraicClosure ℚ_[ℓ])))
      (ψ : R →+* AlgebraicClosure ℚ_[ℓ]),
      ρ.toMonoidHom = (GeneralLinearGroup.map ψ).comp ρuniv.toMonoidHom ∧
        ψ.comp (algebraMap ℤ_[ℓ] R) =
          (algebraMap ℚ_[ℓ] (AlgebraicClosure ℚ_[ℓ])).comp (algebraMap ℤ_[ℓ] ℚ_[ℓ]) := sorry

end AlgebraicGeometry.SchemeOverField
