module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.Finiteness.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.ConstantZMod
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.WeilTrace

/-!
# Étale cohomological traces on curves

This module defines the alternating trace of cyclic-coefficient étale
cohomology on a smooth projective curve and records its degreewise trace
identities.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.AlgebraicCycle AlgebraicGeometry.RelativePicard
open AlgebraicGeometry.AbelianVariety AlgebraicGeometry.Curve
open AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Curve

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- The alternating trace of pullback on degrees `0`, `1`, and `2` of constant
`ZMod m`-coefficient étale cohomology. -/
def etaleLefschetzNumber {C : SchemeOverField k} [Curve C] (φ : C ⟶ C) (m : ℕ) :
    ZMod m :=
  ∑ i : Fin 3, (-1 : ZMod m) ^ (i : ℕ) *
    LinearMap.trace (ZMod m) _ (etaleHq_constantZModMap φ.left m i)

/-- The alternating trace expands as the signed sum over the three
cohomological degrees. -/
theorem etaleLefschetzNumber_eq {C : SchemeOverField k} [Curve C] (φ : C ⟶ C)
    (m : ℕ) :
    etaleLefschetzNumber φ m =
      ∑ i : Fin 3, (-1 : ZMod m) ^ (i : ℕ) *
        LinearMap.trace (ZMod m) _ (etaleHq_constantZModMap φ.left m i) :=
  sorry

/-- On a smooth projective curve, constant `ZMod (ℓ ^ n)`-coefficient étale
cohomology is free when `ℓ` is prime and invertible in the ground field. -/
instance instModuleFree_etaleHq_constantZMod {C : SchemeOverField k} [Curve C]
    [Smooth C.hom] [Projective C.hom] {ℓ n i : ℕ} [Fact ℓ.Prime]
    [Fact (IsUnit (ℓ : k))] :
    Module.Free (ZMod (ℓ ^ n)) (etaleHq_constantZMod C.left (ℓ ^ n) i) :=
  sorry

/-- On a smooth projective curve, constant `ZMod (ℓ ^ n)`-coefficient étale
cohomology is finite when `ℓ` is prime and invertible in the ground field. -/
instance instModuleFinite_etaleHq_constantZMod {C : SchemeOverField k} [Curve C]
    [Smooth C.hom] [Projective C.hom] {ℓ n i : ℕ} [Fact ℓ.Prime]
    [Fact (IsUnit (ℓ : k))] :
    Module.Finite (ZMod (ℓ ^ n)) (etaleHq_constantZMod C.left (ℓ ^ n) i) :=
  sorry

/-- The trace of pullback on degree-zero constant cyclic étale cohomology is
one. -/
theorem etaleHq_constantZModMap_trace_zero {C : SchemeOverField k} [Curve C]
    [Smooth C.hom] [Projective C.hom] (φ : C ⟶ C) (ℓ n : ℕ) [Fact ℓ.Prime]
    (hℓ : IsUnit (ℓ : k)) :
    LinearMap.trace (ZMod (ℓ ^ n)) _ (etaleHq_constantZModMap φ.left (ℓ ^ n) 0) =
      1 :=
  sorry

/-- The trace of pullback on degree-one constant cyclic étale cohomology is
the reduced trace of the induced Jacobian endomorphism. -/
theorem etaleHq_constantZModMap_trace_one {C : SchemeOverField k} [Curve C]
    [Smooth C.hom] [Projective C.hom] (φ : C ⟶ C) (ℓ n : ℕ) [Fact ℓ.Prime]
    (hℓ : IsUnit (ℓ : k)) :
    LinearMap.trace (ZMod (ℓ ^ n)) _ (etaleHq_constantZModMap φ.left (ℓ ^ n) 1) =
      (endomorphismTrace (pullbackComponentHom C φ) : ZMod (ℓ ^ n)) :=
  sorry

/-- The trace of pullback on degree-two constant cyclic étale cohomology is
the reduced degree of the curve endomorphism. -/
theorem etaleHq_constantZModMap_trace_two {C : SchemeOverField k} [Curve C]
    [Smooth C.hom] [Projective C.hom] (φ : C ⟶ C) (ℓ n : ℕ) [Fact ℓ.Prime]
    (hℓ : IsUnit (ℓ : k)) :
    LinearMap.trace (ZMod (ℓ ^ n)) _ (etaleHq_constantZModMap φ.left (ℓ ^ n) 2) =
      (curveEndomorphismDegree φ : ZMod (ℓ ^ n)) :=
  sorry

/-- For a non-identity endomorphism of a smooth projective curve, the
alternating cyclic étale cohomological trace equals the fixed-point number. -/
theorem weilTraceFormula_etale (C : SchemeOverField k) [Curve C] [Smooth C.hom]
    [Projective C.hom] (φ : C ⟶ C) (hφ : φ ≠ 𝟙 C) (ℓ n : ℕ) [Fact ℓ.Prime]
    (hℓ : IsUnit (ℓ : k)) :
    etaleLefschetzNumber φ (ℓ ^ n) = (fixedPointNumber φ hφ : ZMod (ℓ ^ n)) :=
  sorry

end AlgebraicGeometry.Curve
