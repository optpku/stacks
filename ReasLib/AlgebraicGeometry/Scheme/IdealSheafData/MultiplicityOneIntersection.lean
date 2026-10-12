/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Intersection
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.IntersectionCycle
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.IntersectionMultiplicity
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary.Affine
public import ReasLib.RingTheory.Catenary.Field

/-!
# Multiplicity-one components of scheme-theoretic intersections

This module records the associated-cycle consequences of a multiplicity-one
component in a proper intersection of closed subschemes.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData.AssociatedCycle

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : SchemeOverField k) [Variety X] [Scheme.Regular X.left]
  (r s : ℕ) (Y Z : X.left.IdealSheafData)
  (hY : X.hom.closedSubschemeDeltaDimension (fun _ ↦ 0) Y ≤ ((r : ℤ) : EInt))
  (hZ : X.hom.closedSubschemeDeltaDimension (fun _ ↦ 0) Z ≤ ((s : ℤ) : EInt))

/-- A multiplicity-one component of a proper intersection has coefficient one in the
associated-cycle intersection. -/
theorem intersectionCoefficient_eq_one_of_componentMultiplicity_eq_one :
    let alpha : AlgebraicCycle X.left ℤ :=
      X.hom.closedSubschemeCycle (fun _ ↦ 0) Y (r : ℤ) hY
    let beta : AlgebraicCycle X.left ℤ :=
      X.hom.closedSubschemeCycle (fun _ ↦ 0) Z (s : ℤ) hZ
    ∀ (hproper : alpha.IntersectProperly beta) (x y : X.left)
      (hx : alpha x ≠ 0) (hy : beta y ≠ 0),
      let P := (Scheme.PointClosure.reducedStructure x).ideal ⊔
        (Scheme.PointClosure.reducedStructure y).ideal
      ∀ (tau : genericPoints P.subscheme) (xi : genericPoints (Y ⊔ Z).subscheme)
        (hT : P.subschemeι tau.1 = (Y ⊔ Z).subschemeι xi.1)
        (hmult : componentMultiplicity (Y ⊔ Z) xi = 1),
        AlgebraicCycle.intersection alpha beta hproper (P.subschemeι tau.1) = 1 := sorry

/-- The left closed subscheme is smooth at a multiplicity-one intersection component. -/
theorem leftSmoothAt_of_componentMultiplicity_eq_one :
    let alpha : AlgebraicCycle X.left ℤ :=
      X.hom.closedSubschemeCycle (fun _ ↦ 0) Y (r : ℤ) hY
    let beta : AlgebraicCycle X.left ℤ :=
      X.hom.closedSubschemeCycle (fun _ ↦ 0) Z (s : ℤ) hZ
    ∀ (hproper : alpha.IntersectProperly beta) (x y : X.left)
      (hx : alpha x ≠ 0) (hy : beta y ≠ 0),
      let P := (Scheme.PointClosure.reducedStructure x).ideal ⊔
        (Scheme.PointClosure.reducedStructure y).ideal
      ∀ (tau : genericPoints P.subscheme) (xi : genericPoints (Y ⊔ Z).subscheme)
        (hT : P.subschemeι tau.1 = (Y ⊔ Z).subschemeι xi.1)
        (hmult : componentMultiplicity (Y ⊔ Z) xi = 1),
        (Y.subschemeι ≫ X.hom).SmoothAt
          ((inclusion (le_sup_left : Y ≤ Y ⊔ Z)).base xi.1) := sorry

/-- The right closed subscheme is smooth at a multiplicity-one intersection component. -/
theorem rightSmoothAt_of_componentMultiplicity_eq_one :
    let alpha : AlgebraicCycle X.left ℤ :=
      X.hom.closedSubschemeCycle (fun _ ↦ 0) Y (r : ℤ) hY
    let beta : AlgebraicCycle X.left ℤ :=
      X.hom.closedSubschemeCycle (fun _ ↦ 0) Z (s : ℤ) hZ
    ∀ (hproper : alpha.IntersectProperly beta) (x y : X.left)
      (hx : alpha x ≠ 0) (hy : beta y ≠ 0),
      let P := (Scheme.PointClosure.reducedStructure x).ideal ⊔
        (Scheme.PointClosure.reducedStructure y).ideal
      ∀ (tau : genericPoints P.subscheme) (xi : genericPoints (Y ⊔ Z).subscheme)
        (hT : P.subschemeι tau.1 = (Y ⊔ Z).subschemeι xi.1)
        (hmult : componentMultiplicity (Y ⊔ Z) xi = 1),
        (Z.subschemeι ≫ X.hom).SmoothAt
          ((inclusion (le_sup_right : Z ≤ Y ⊔ Z)).base xi.1) := sorry

/-- The selected component has coefficient one in the left associated cycle. -/
theorem leftCoefficient_eq_one_of_componentMultiplicity_eq_one :
    let alpha : AlgebraicCycle X.left ℤ :=
      X.hom.closedSubschemeCycle (fun _ ↦ 0) Y (r : ℤ) hY
    let beta : AlgebraicCycle X.left ℤ :=
      X.hom.closedSubschemeCycle (fun _ ↦ 0) Z (s : ℤ) hZ
    ∀ (hproper : alpha.IntersectProperly beta) (x y : X.left)
      (hx : alpha x ≠ 0) (hy : beta y ≠ 0),
      let P := (Scheme.PointClosure.reducedStructure x).ideal ⊔
        (Scheme.PointClosure.reducedStructure y).ideal
      ∀ (tau : genericPoints P.subscheme) (xi : genericPoints (Y ⊔ Z).subscheme)
        (hT : P.subschemeι tau.1 = (Y ⊔ Z).subschemeι xi.1)
        (hmult : componentMultiplicity (Y ⊔ Z) xi = 1),
        alpha x = 1 := sorry

/-- The selected component has coefficient one in the right associated cycle. -/
theorem rightCoefficient_eq_one_of_componentMultiplicity_eq_one :
    let alpha : AlgebraicCycle X.left ℤ :=
      X.hom.closedSubschemeCycle (fun _ ↦ 0) Y (r : ℤ) hY
    let beta : AlgebraicCycle X.left ℤ :=
      X.hom.closedSubschemeCycle (fun _ ↦ 0) Z (s : ℤ) hZ
    ∀ (hproper : alpha.IntersectProperly beta) (x y : X.left)
      (hx : alpha x ≠ 0) (hy : beta y ≠ 0),
      let P := (Scheme.PointClosure.reducedStructure x).ideal ⊔
        (Scheme.PointClosure.reducedStructure y).ideal
      ∀ (tau : genericPoints P.subscheme) (xi : genericPoints (Y ⊔ Z).subscheme)
        (hT : P.subschemeι tau.1 = (Y ⊔ Z).subschemeι xi.1)
        (hmult : componentMultiplicity (Y ⊔ Z) xi = 1),
        beta y = 1 := sorry

/-- The selected intersection component is not contained in any other left
component with nonzero associated-cycle coefficient. -/
theorem intersectionComponent_avoidsOtherLeftComponents :
    let alpha : AlgebraicCycle X.left ℤ :=
      X.hom.closedSubschemeCycle (fun _ ↦ 0) Y (r : ℤ) hY
    let beta : AlgebraicCycle X.left ℤ :=
      X.hom.closedSubschemeCycle (fun _ ↦ 0) Z (s : ℤ) hZ
    ∀ (hproper : alpha.IntersectProperly beta) (x y : X.left)
      (hx : alpha x ≠ 0) (hy : beta y ≠ 0),
      let P := (Scheme.PointClosure.reducedStructure x).ideal ⊔
        (Scheme.PointClosure.reducedStructure y).ideal
      ∀ (tau : genericPoints P.subscheme) (xi : genericPoints (Y ⊔ Z).subscheme)
        (hT : P.subschemeι tau.1 = (Y ⊔ Z).subschemeι xi.1)
        (hmult : componentMultiplicity (Y ⊔ Z) xi = 1)
        (x' : X.left) (hx' : alpha x' ≠ 0) (hne : x' ≠ x),
        P.subschemeι tau.1 ∉ Scheme.PointClosure.closedSubset x' := sorry

/-- The selected intersection component is not contained in any other right
component with nonzero associated-cycle coefficient. -/
theorem intersectionComponent_avoidsOtherRightComponents :
    let alpha : AlgebraicCycle X.left ℤ :=
      X.hom.closedSubschemeCycle (fun _ ↦ 0) Y (r : ℤ) hY
    let beta : AlgebraicCycle X.left ℤ :=
      X.hom.closedSubschemeCycle (fun _ ↦ 0) Z (s : ℤ) hZ
    ∀ (hproper : alpha.IntersectProperly beta) (x y : X.left)
      (hx : alpha x ≠ 0) (hy : beta y ≠ 0),
      let P := (Scheme.PointClosure.reducedStructure x).ideal ⊔
        (Scheme.PointClosure.reducedStructure y).ideal
      ∀ (tau : genericPoints P.subscheme) (xi : genericPoints (Y ⊔ Z).subscheme)
        (hT : P.subschemeι tau.1 = (Y ⊔ Z).subschemeι xi.1)
        (hmult : componentMultiplicity (Y ⊔ Z) xi = 1)
        (y' : X.left) (hy' : beta y' ≠ 0) (hne : y' ≠ y),
        P.subschemeι tau.1 ∉ Scheme.PointClosure.closedSubset y' := sorry

end AlgebraicGeometry.Scheme.IdealSheafData.AssociatedCycle
