module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.MultiplicityOneIntersection

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open Scheme.IdealSheafData
open scoped AlgebraicGeometry

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
  (X : SchemeOverField k) [Variety X] [Scheme.Regular X.left]
  (r s : ℕ) (Y Z : X.left.IdealSheafData)
  (hY : X.hom.closedSubschemeDeltaDimension (fun _ ↦ 0) Y ≤ ((r : ℤ) : EInt))
  (hZ : X.hom.closedSubschemeDeltaDimension (fun _ ↦ 0) Z ≤ ((s : ℤ) : EInt))

/- Lemma 43.17.2 (1): a multiplicity-one component of the scheme-theoretic
intersection has coefficient one in the product of the associated cycles. -/
@[stacks 0B1J] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.AssociatedCycle.intersectionCoefficient_eq_one_of_componentMultiplicity_eq_one
      X r s Y Z hY hZ :
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
        AlgebraicCycle.intersection alpha beta hproper (P.subschemeι tau.1) = 1)

/- Lemma 43.17.2 (2): the left closed subscheme is nonsingular at the generic
point of the multiplicity-one intersection component. -/
@[stacks 0B1J] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.AssociatedCycle.leftSmoothAt_of_componentMultiplicity_eq_one
      X r s Y Z hY hZ :
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
          ((inclusion (le_sup_left : Y ≤ Y ⊔ Z)).base xi.1))

/- Lemma 43.17.2 (3): the right closed subscheme is nonsingular at the generic
point of the multiplicity-one intersection component. -/
@[stacks 0B1J] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.AssociatedCycle.rightSmoothAt_of_componentMultiplicity_eq_one
      X r s Y Z hY hZ :
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
          ((inclusion (le_sup_right : Z ≤ Y ⊔ Z)).base xi.1))

/- Lemma 43.17.2 (4): the selected component of the left associated cycle has
coefficient one. -/
@[stacks 0B1J] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.AssociatedCycle.leftCoefficient_eq_one_of_componentMultiplicity_eq_one
      X r s Y Z hY hZ :
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
        alpha x = 1)

/- Lemma 43.17.2 (5): the selected component of the right associated cycle has
coefficient one. -/
@[stacks 0B1J] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.AssociatedCycle.rightCoefficient_eq_one_of_componentMultiplicity_eq_one
      X r s Y Z hY hZ :
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
        beta y = 1)

/- Lemma 43.17.2 (6): the selected intersection component is not contained in
any other component occurring in the left associated cycle. -/
@[stacks 0B1J] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.AssociatedCycle.intersectionComponent_avoidsOtherLeftComponents
      X r s Y Z hY hZ :
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
        P.subschemeι tau.1 ∉ Scheme.PointClosure.closedSubset x')

/- Lemma 43.17.2 (7): the selected intersection component is not contained in
any other component occurring in the right associated cycle. -/
@[stacks 0B1J] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.AssociatedCycle.intersectionComponent_avoidsOtherRightComponents
      X r s Y Z hY hZ :
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
        P.subschemeι tau.1 ∉ Scheme.PointClosure.closedSubset y')
