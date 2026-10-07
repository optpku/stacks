module

public import Mathlib.Algebra.CharP.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap64.Theorem_64_31_10_DeJong
public import stacks_project.Chap64.Theorem_64_31_10_Deformation
public import stacks_project.Chap64.Theorem_64_31_10_GLRep

/-!
# Finite flatness of universal deformation rings of residual representations
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
open Deformation IsLocalRing Matrix Matrix.GeneralLinearGroup

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- Theorem 64.31.10 (1). Let `k` be a finite field of characteristic `p`, and let `X` be a
geometrically irreducible smooth projective curve over `k`. Let
`ρ₀ : etaleFundamentalGroup X.left (arithmeticPoint X xbar) →ₜ* GL (Fin n) (ZMod ℓ)`
be continuous with `ℓ ≠ p`. Assume de Jong's conjecture holds for `X` at the prime `ℓ` and rank
`n`, that the restriction of `ρ₀` to `etaleFundamentalGroup (geometricBaseChange X) xbar` is
absolutely irreducible, and that `ℓ` does not divide `n`. Then any universal deformation ring of
`ρ₀` is finite as a `ℤ_[ℓ]`-module. -/
@[stacks 03W1]
theorem universalDeformationRing_moduleFinite
    {k : Type u} [Field k] [Finite k] {p ℓ n : ℕ} [Fact p.Prime] [Fact ℓ.Prime] [CharP k p]
    (hℓp : ℓ ≠ p) (hℓn : ¬ ℓ ∣ n) (X : SchemeOverField k)
    [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
    [ConnectedSpace (geometricBaseChange X)]
    (xbar : GeometricPoint (geometricBaseChange X))
    (hconj : deJongConjectureAt X xbar ℓ n)
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
    Module.Finite ℤ_[ℓ] R := sorry

/-- Theorem 64.31.10 (2). Under the same hypotheses as `universalDeformationRing_moduleFinite`,
any universal deformation ring of `ρ₀` is flat as a `ℤ_[ℓ]`-module. -/
@[stacks 03W1]
theorem universalDeformationRing_moduleFlat
    {k : Type u} [Field k] [Finite k] {p ℓ n : ℕ} [Fact p.Prime] [Fact ℓ.Prime] [CharP k p]
    (hℓp : ℓ ≠ p) (hℓn : ¬ ℓ ∣ n) (X : SchemeOverField k)
    [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
    [ConnectedSpace (geometricBaseChange X)]
    (xbar : GeometricPoint (geometricBaseChange X))
    (hconj : deJongConjectureAt X xbar ℓ n)
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

/-- In particular, such a residual representation lifts to a continuous homomorphism
into `GL (Fin n)` of an algebraic closure of `ℚ_[ℓ]`. -/
theorem exists_qlBarLift
    {k : Type u} [Field k] [Finite k] {p ℓ n : ℕ} [Fact p.Prime] [Fact ℓ.Prime] [CharP k p]
    (hℓp : ℓ ≠ p) (hℓn : ¬ ℓ ∣ n) (X : SchemeOverField k)
    [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
    [ConnectedSpace (geometricBaseChange X)]
    (xbar : GeometricPoint (geometricBaseChange X))
    (hconj : deJongConjectureAt X xbar ℓ n)
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
