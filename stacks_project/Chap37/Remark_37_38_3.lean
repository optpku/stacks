/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import stacks_project.Chap37.Lemma_37_38_2
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Slicing.InseparablePlane

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.InseparablePlanePoint

#check (AlgebraicGeometry.InseparablePlanePoint.projection_smooth :
  ∀ (k : Type u) [Field k], Smooth (projection k))

#check (AlgebraicGeometry.InseparablePlanePoint.pointResidueFieldMap_isPurelyInseparable :
  ∀ (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] (a : k)
      (ha : a ∉ Set.range (fun b : k ↦ b ^ p)),
      ((projection k).residueFieldMap
        (point p k a ha).toPrimeSpectrum).hom.IsPurelyInseparable)

#check (AlgebraicGeometry.InseparablePlanePoint.pointResidueField_notSeparable :
  ∀ (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] (a : k)
      (ha : a ∉ Set.range (fun b : k ↦ b ^ p)),
    ¬ Algebra.IsSeparable
      ((Spec (CommRingCat.of (Polynomial k))).residueField
        (projection k (point p k a ha).toPrimeSpectrum))
      ((Spec (CommRingCat.of (MvPolynomial (Fin 2) k))).residueField
        (point p k a ha).toPrimeSpectrum))

#check (AlgebraicGeometry.InseparablePlanePoint.point_mem_closedPoints :
  ∀ (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] (a : k)
      (ha : a ∉ Set.range (fun b : k ↦ b ^ p)),
    (point p k a ha).toPrimeSpectrum ∈
      closedPoints (Spec (CommRingCat.of (MvPolynomial (Fin 2) k))))

#check (AlgebraicGeometry.InseparablePlanePoint.fiberDimensionAt_pos :
  ∀ (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] (a : k)
      (ha : a ∉ Set.range (fun b : k ↦ b ^ p)),
    0 < (projection k).fiberDimensionAt (point p k a ha).toPrimeSpectrum)

/- Remark 37.38.3: for the point `(x, y ^ p - a)` of the affine plane in characteristic
`p`, the smooth projection to the affine line admits no compatible étale lift through the
point. -/
@[stacks 057E] #check
  (AlgebraicGeometry.InseparablePlanePoint.noEtaleLift :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] (a : k)
        (ha : a ∉ Set.range (fun b : k ↦ b ^ p)),
      ¬ ∃ (S' : Scheme.{u})
          (g : S' ⟶ Spec (CommRingCat.of (Polynomial k)))
          (h : S' ⟶ Spec (CommRingCat.of (MvPolynomial (Fin 2) k))),
        Etale g ∧ h ≫ projection k = g ∧
          (point p k a ha).toPrimeSpectrum ∈ Set.range h)

end AlgebraicGeometry.InseparablePlanePoint
