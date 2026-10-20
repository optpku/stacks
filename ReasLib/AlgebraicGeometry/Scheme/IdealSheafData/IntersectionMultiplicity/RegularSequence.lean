/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.IdealSubobject.Kernel
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.IdealStalk
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.IntersectionMultiplicity
public import ReasLib.RingTheory.Ideal.HilbertSamuel.Multiplicity
public import ReasLib.RingTheory.Ideal.HilbertSamuel.TorMultiplicity

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {k : Type u} [Field k] (X : SchemeOverField k) [Variety X]
  [Scheme.Regular X.left] (V W : X.left.IdealSheafData)
  [IsIntegral V.subscheme] [IsIntegral W.subscheme]

/-- The local intersection multiplicity at a properly intersecting component agrees with
the degree-indexed Hilbert--Samuel multiplicity of the stalk ideal of `V` acting on the
ambient-stalk quotient presenting the local ring of `W`. -/
theorem intersectionMultiplicity_eq_multiplicityInDegree
    (hproper : Closeds.IntersectProperly V.support W.support)
    (Z : irreducibleComponents (V ⊔ W).subscheme) (c : ℕ) :
    let Y := X.left
    let ξ := genericPoints.ofComponent Z
    let x := (V ⊔ W).subschemeι ξ.1
    let R := Y.presheaf.stalk x
    let I := RingedSpace.idealSheafStalkIdeal
      (LocallyRingedSpace.closedImmersionIdealSubobject V.subschemeι.toLRSHom) x
    let J := RingedSpace.idealSheafStalkIdeal
      (LocallyRingedSpace.closedImmersionIdealSubobject W.subschemeι.toLRSHom) x
    let M := R ⧸ J
    ∀ (f : Fin c → R)
      (hreg : RingTheory.Sequence.IsRegular R (List.ofFn f))
      (hgen : Ideal.span (Set.range f) = I),
      (V.intersectionMultiplicity W ξ : ℚ) =
        Ideal.HilbertSamuel.multiplicityInDegree I M c := sorry

/-- At a properly intersecting component, a regular-sequence presentation of the stalk
ideal computes the local intersection multiplicity as the sequence-length factorial times
the leading coefficient of an eventual quotient-length polynomial. -/
theorem intersectionMultiplicity_eq_factorial_mul_leadingCoeff
    (hproper : Closeds.IntersectProperly V.support W.support)
    (Z : irreducibleComponents (V ⊔ W).subscheme) (c : ℕ) :
    let Y := X.left
    let ξ := genericPoints.ofComponent Z
    let x := (V ⊔ W).subschemeι ξ.1
    let R := Y.presheaf.stalk x
    let I := RingedSpace.idealSheafStalkIdeal
      (LocallyRingedSpace.closedImmersionIdealSubobject V.subschemeι.toLRSHom) x
    let J := RingedSpace.idealSheafStalkIdeal
      (LocallyRingedSpace.closedImmersionIdealSubobject W.subschemeι.toLRSHom) x
    let M := R ⧸ J
    ∀ (f : Fin c → R)
      (hreg : RingTheory.Sequence.IsRegular R (List.ofFn f))
      (hgen : Ideal.span (Set.range f) = I)
      (P : Polynomial ℚ)
      (hP : P.EventuallyEqNat (fun t ↦
        ((Module.length R
          (M ⧸ (I ^ t • ⊤ : Submodule R M))).toNat : ℚ))),
      (V.intersectionMultiplicity W ξ : ℚ) =
        (c.factorial : ℚ) * P.leadingCoeff := sorry

/-- The leading coefficient of the eventual quotient-length polynomial attached to a
regular-sequence presentation at a properly intersecting component is strictly positive. -/
theorem intersectionHilbertPolynomial_leadingCoeff_pos
    (hproper : Closeds.IntersectProperly V.support W.support)
    (Z : irreducibleComponents (V ⊔ W).subscheme) (c : ℕ) :
    let Y := X.left
    let ξ := genericPoints.ofComponent Z
    let x := (V ⊔ W).subschemeι ξ.1
    let R := Y.presheaf.stalk x
    let I := RingedSpace.idealSheafStalkIdeal
      (LocallyRingedSpace.closedImmersionIdealSubobject V.subschemeι.toLRSHom) x
    let J := RingedSpace.idealSheafStalkIdeal
      (LocallyRingedSpace.closedImmersionIdealSubobject W.subschemeι.toLRSHom) x
    let M := R ⧸ J
    ∀ (f : Fin c → R)
      (hreg : RingTheory.Sequence.IsRegular R (List.ofFn f))
      (hgen : Ideal.span (Set.range f) = I)
      (P : Polynomial ℚ)
      (hP : P.EventuallyEqNat (fun t ↦
        ((Module.length R
          (M ⧸ (I ^ t • ⊤ : Submodule R M))).toNat : ℚ))),
      0 < P.leadingCoeff := sorry

/-- For a regular-sequence presentation of a stalk ideal at a properly intersecting
component, the local intersection multiplicity has the factorial leading-coefficient
formula and that leading coefficient is positive. -/
theorem intersectionMultiplicity_regularSequence_spec
    (hproper : Closeds.IntersectProperly V.support W.support)
    (Z : irreducibleComponents (V ⊔ W).subscheme) (c : ℕ) :
    let Y := X.left
    let ξ := genericPoints.ofComponent Z
    let x := (V ⊔ W).subschemeι ξ.1
    let R := Y.presheaf.stalk x
    let I := RingedSpace.idealSheafStalkIdeal
      (LocallyRingedSpace.closedImmersionIdealSubobject V.subschemeι.toLRSHom) x
    let J := RingedSpace.idealSheafStalkIdeal
      (LocallyRingedSpace.closedImmersionIdealSubobject W.subschemeι.toLRSHom) x
    let M := R ⧸ J
    ∀ (f : Fin c → R)
      (hreg : RingTheory.Sequence.IsRegular R (List.ofFn f))
      (hgen : Ideal.span (Set.range f) = I)
      (P : Polynomial ℚ)
      (hP : P.EventuallyEqNat (fun t ↦
        ((Module.length R
          (M ⧸ (I ^ t • ⊤ : Submodule R M))).toNat : ℚ))),
      (V.intersectionMultiplicity W ξ : ℚ) =
          (c.factorial : ℚ) * P.leadingCoeff ∧
        0 < P.leadingCoeff := sorry

end AlgebraicGeometry.Scheme.IdealSheafData
