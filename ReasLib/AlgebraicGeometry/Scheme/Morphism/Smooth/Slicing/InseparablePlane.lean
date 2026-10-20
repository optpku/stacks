module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Fiber
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Spectrum.Maximal.Topology

/-!
# An inseparable point of the affine plane

This file constructs a closed point on a positive-dimensional fibre of the
smooth affine-plane projection which admits no compatible lift from a scheme
étale over the affine line.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.InseparablePlanePoint

variable (p : ℕ) [Fact p.Prime]

/-- The ideal `(x, y ^ p - a)` defining the distinguished affine-plane point. -/
def pointIdeal (k : Type u) [Field k] (a : k) :
    Ideal (MvPolynomial (Fin 2) k) :=
  Ideal.span {MvPolynomial.X (0 : Fin 2),
    MvPolynomial.X (1 : Fin 2) ^ p - MvPolynomial.C a}

/-- The distinguished ideal is the span of `x` and `y ^ p - a`. -/
theorem pointIdeal_eq_span (k : Type u) [Field k] (a : k) :
    pointIdeal p k a =
      Ideal.span {MvPolynomial.X (0 : Fin 2),
        MvPolynomial.X (1 : Fin 2) ^ p - MvPolynomial.C a} := sorry

/-- If `a` is not a `p`-th power, the ideal `(x, y ^ p - a)` is maximal. -/
theorem pointIdeal_isMaximal (k : Type u) [Field k] [CharP k p] (a : k)
    (ha : a ∉ Set.range (fun b : k ↦ b ^ p)) :
    (pointIdeal p k a).IsMaximal := sorry

/-- The maximal-spectrum point represented by `(x, y ^ p - a)`. -/
def point (k : Type u) [Field k] [CharP k p] (a : k)
    (ha : a ∉ Set.range (fun b : k ↦ b ^ p)) :
    MaximalSpectrum (MvPolynomial (Fin 2) k) :=
  ⟨pointIdeal p k a, pointIdeal_isMaximal p k a ha⟩

/-- The ideal underlying the distinguished maximal-spectrum point. -/
theorem point_asIdeal (k : Type u) [Field k] [CharP k p] (a : k)
    (ha : a ∉ Set.range (fun b : k ↦ b ^ p)) :
    (point p k a ha).asIdeal = pointIdeal p k a := sorry

/-- The coordinate-ring map `k[x] → k[x, y]` sending `x` to the first coordinate. -/
def projectionRingHom (k : Type u) [Field k] :
    Polynomial k →+* MvPolynomial (Fin 2) k :=
  Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X (0 : Fin 2))

/-- The coordinate-ring map sends `Polynomial.X` to the first plane coordinate. -/
theorem projectionRingHom_X (k : Type u) [Field k] :
    projectionRingHom k Polynomial.X = MvPolynomial.X (0 : Fin 2) := sorry

/-- The affine-plane projection induced by `k[x] → k[x, y]`. -/
def projection (k : Type u) [Field k] :
    Spec (CommRingCat.of (MvPolynomial (Fin 2) k)) ⟶
      Spec (CommRingCat.of (Polynomial k)) :=
  Spec.map (CommRingCat.ofHom (projectionRingHom k))

/-- The projection acts on points by contraction along `projectionRingHom`. -/
theorem projection_apply (k : Type u) [Field k]
    (x : PrimeSpectrum (MvPolynomial (Fin 2) k)) :
    projection k x = PrimeSpectrum.comap (projectionRingHom k) x := sorry

/-- The affine-plane projection is smooth. -/
instance projection_smooth (k : Type u) [Field k] : Smooth (projection k) := sorry

/-- The residue-field map at the distinguished point is purely inseparable. -/
theorem pointResidueFieldMap_isPurelyInseparable
    (k : Type u) [Field k] [CharP k p] (a : k)
    (ha : a ∉ Set.range (fun b : k ↦ b ^ p)) :
    ((projection k).residueFieldMap
      (point p k a ha).toPrimeSpectrum).hom.IsPurelyInseparable := sorry

/-- The residue field at the distinguished point is not separable over that of its image. -/
theorem pointResidueField_notSeparable
    (k : Type u) [Field k] [CharP k p] (a : k)
    (ha : a ∉ Set.range (fun b : k ↦ b ^ p)) :
    ¬ Algebra.IsSeparable
      ((Spec (CommRingCat.of (Polynomial k))).residueField
        (projection k (point p k a ha).toPrimeSpectrum))
      ((Spec (CommRingCat.of (MvPolynomial (Fin 2) k))).residueField
        (point p k a ha).toPrimeSpectrum) := sorry

/-- The point `(x, y ^ p - a)` is closed in the affine plane. -/
theorem point_mem_closedPoints
    (k : Type u) [Field k] [CharP k p] (a : k)
    (ha : a ∉ Set.range (fun b : k ↦ b ^ p)) :
    (point p k a ha).toPrimeSpectrum ∈
      closedPoints (Spec (CommRingCat.of (MvPolynomial (Fin 2) k))) := sorry

/-- The distinguished point lies on a positive-dimensional fibre. -/
theorem fiberDimensionAt_pos
    (k : Type u) [Field k] [CharP k p] (a : k)
    (ha : a ∉ Set.range (fun b : k ↦ b ^ p)) :
    0 < (projection k).fiberDimensionAt
      (point p k a ha).toPrimeSpectrum := sorry

/-- The distinguished point is not in the image of a morphism from an étale scheme over the
affine line that is compatible with the affine-plane projection. -/
@[stacks 057E]
theorem noEtaleLift
    (k : Type u) [Field k] [CharP k p] (a : k)
    (ha : a ∉ Set.range (fun b : k ↦ b ^ p)) :
    ¬ ∃ (S' : Scheme.{u})
        (g : S' ⟶ Spec (CommRingCat.of (Polynomial k)))
        (h : S' ⟶ Spec (CommRingCat.of (MvPolynomial (Fin 2) k))),
      Etale g ∧ h ≫ projection k = g ∧
        (point p k a ha).toPrimeSpectrum ∈ Set.range h := sorry

end AlgebraicGeometry.InseparablePlanePoint
