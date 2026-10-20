module

public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.WeilTrace
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicCycle AlgebraicGeometry.RelativePicard
open AlgebraicGeometry.AbelianVariety AlgebraicGeometry.Curve
open scoped AlgebraicGeometry CategoryTheory.MonObj

universe u

/- Theorem 64.14.4 (Weil): the diagonal-graph intersection number of a
non-identity endomorphism of a nonsingular projective curve equals
`1 - Tr_J(φ*) + deg φ`. -/

@[stacks 03U1]
#check (AlgebraicGeometry.Curve.weilTraceFormula :
  ∀ {k : Type u} [Field k] [IsAlgClosed k]
    (C : SchemeOverField k) [Curve C] [Smooth C.hom] [Projective C.hom]
    (φ : C ⟶ C) (hφ : φ ≠ 𝟙 C),
    fixedPointNumber φ hφ =
      1 - endomorphismTrace (pullbackComponentHom C φ) +
        (curveEndomorphismDegree φ : ℤ))

#check (AlgebraicGeometry.Curve.weilTraceFormula_mod :
  ∀ {k : Type u} [Field k] [IsAlgClosed k]
    (C : SchemeOverField k) [Curve C] [Smooth C.hom] [Projective C.hom]
    (φ : C ⟶ C) (hφ : φ ≠ 𝟙 C) (ℓ : ℕ) [NeZero ℓ]
    (hℓ : IsUnit (ℓ : k)),
    (fixedPointNumber φ hφ : ZMod ℓ) =
      1 - LinearMap.trace (ZMod ℓ) _
          (rationalTorsionMap (pullbackComponentHom C φ) ℓ) +
        (curveEndomorphismDegree φ : ZMod ℓ))
