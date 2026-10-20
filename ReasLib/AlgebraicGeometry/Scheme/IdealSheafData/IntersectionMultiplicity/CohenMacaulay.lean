/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.IntersectionCycle
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.IntersectionMultiplicity.RegularSequence

/-!
# Intersection multiplicities of Cohen–Macaulay closed subschemes

This module compares Serre intersection multiplicities with component multiplicities when
the two local rings are Cohen–Macaulay and records the corresponding equality of cycles.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open TopCat.Presheaf
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {k : Type u} [Field k] (X : SchemeOverField k) [Variety X]
  [Scheme.Regular X.left] (V W : X.left.IdealSheafData)
  [IsIntegral V.subscheme] [IsIntegral W.subscheme]

/-- At a component where both closed subschemes have Cohen–Macaulay local rings, their
Serre intersection multiplicity is the component multiplicity of the scheme-theoretic
intersection. -/
theorem intersectionMultiplicity_eq_componentMultiplicity_of_cohenMacaulay
    (hproper : Closeds.IntersectProperly V.support W.support)
    (Z : irreducibleComponents (V ⊔ W).subscheme)
    [hV : CohenMacaulayRing
      (stalk V.subscheme.presheaf
        ((inclusion (le_sup_left : V ≤ V ⊔ W)).base
          (genericPoints.ofComponent Z).1) : CommRingCat)]
    [hW : CohenMacaulayRing
      (stalk W.subscheme.presheaf
        ((inclusion (le_sup_right : W ≤ V ⊔ W)).base
          (genericPoints.ofComponent Z).1) : CommRingCat)] :
    V.intersectionMultiplicity W (genericPoints.ofComponent Z) =
      ((V ⊔ W).componentMultiplicity (genericPoints.ofComponent Z) : ℤ) := sorry

/-- If two properly intersecting integral closed subschemes are Cohen–Macaulay, their
intersection cycle is the expected-dimensional associated cycle of their scheme-theoretic
intersection. -/
theorem intersectionCycle_eq_associatedCycle_of_cohenMacaulay
    [Scheme.CohenMacaulay V.subscheme] [Scheme.CohenMacaulay W.subscheme]
    (hproper : Closeds.IntersectProperly V.support W.support) :
    intersectionCycle V W hproper =
      ((V ⊔ W).associatedCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0))
        (expectedIntersectionDimension X V W) : AlgebraicCycle X.left ℤ) := sorry

/-- If the local ring of one member of a proper intersection is Cohen--Macaulay, then a
regular sequence generating the other member's stalk ideal computes the local intersection
multiplicity as the length of the resulting quotient. -/
theorem intersectionMultiplicity_eq_length_quotient_of_cohenMacaulay
    (hproper : Closeds.IntersectProperly V.support W.support)
    (Z : irreducibleComponents (V ⊔ W).subscheme) (c : ℕ)
    [hW : CohenMacaulayRing
      (stalk W.subscheme.presheaf
        ((inclusion (le_sup_right : W ≤ V ⊔ W)).base
          (genericPoints.ofComponent Z).1) : CommRingCat)] :
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
      V.intersectionMultiplicity W ξ =
        ((Module.length R (M ⧸ (I • ⊤ : Submodule R M))).toNat : ℤ) := sorry

end AlgebraicGeometry.Scheme.IdealSheafData
