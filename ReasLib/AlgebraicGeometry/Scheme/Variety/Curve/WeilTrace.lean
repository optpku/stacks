module

public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Trace
public import ReasLib.AlgebraicGeometry.GroupScheme.AbelianVariety.Trace
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Relative.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Endomorphism

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicCycle AlgebraicGeometry.RelativePicard
open AlgebraicGeometry.AbelianVariety AlgebraicGeometry.Curve
open scoped AlgebraicGeometry CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.Curve

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- For a non-identity endomorphism of a smooth projective curve, the
diagonal-graph intersection number equals one minus the Jacobian trace plus
the endomorphism degree. -/
theorem weilTraceFormula (C : SchemeOverField k) [Curve C] [Smooth C.hom]
    [Projective C.hom] (φ : C ⟶ C) (hφ : φ ≠ 𝟙 C) :
    fixedPointNumber φ hφ =
      1 - endomorphismTrace (pullbackComponentHom C φ) +
        (curveEndomorphismDegree φ : ℤ) := sorry

/-- The Weil identity reduced modulo a nonzero integer invertible in the field. -/
theorem weilTraceFormula_mod (C : SchemeOverField k) [Curve C] [Smooth C.hom]
    [Projective C.hom] (φ : C ⟶ C) (hφ : φ ≠ 𝟙 C)
    (ℓ : ℕ) [NeZero ℓ] (hℓ : IsUnit (ℓ : k)) :
    (fixedPointNumber φ hφ : ZMod ℓ) =
      1 - LinearMap.trace (ZMod ℓ) _
          (rationalTorsionMap (pullbackComponentHom C φ) ℓ) +
        (curveEndomorphismDegree φ : ZMod ℓ) := sorry

end AlgebraicGeometry.Curve
