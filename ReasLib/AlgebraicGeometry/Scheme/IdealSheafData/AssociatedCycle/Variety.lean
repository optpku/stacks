/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.ProperIntersection
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.AssociatedCycle
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Product
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary.Affine
public import ReasLib.RingTheory.Catenary.Field

/-!
# Associated cycles of closed subvarieties

This module defines the intrinsic-dimensional cycle of a closed subvariety and
relates proper intersection of closed supports to proper intersection of cycles.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

/-- The algebraic cycle associated to an integral closed subvariety in its intrinsic
dimension. -/
noncomputable def subvarietyCycle (X : SchemeOverField k) [Variety X]
    (Z : X.left.IdealSheafData) [Variety (Over.mk (Z.subschemeι ≫ X.hom))] :
    AlgebraicCycle X.left ℤ :=
  CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0))
    (dimension (Over.mk (Z.subschemeι ≫ X.hom)) : ℤ)
    (@Scheme.IdealSheafData.associatedCycle X.left
      (@LocallyOfFiniteType.isLocallyNoetherian X.left _ X.hom inferInstance
        (@UniversallyCatenary.toIsLocallyNoetherian _
          (@instUniversallyCatenarySpec.{u} k inferInstance
            (@instUniversallyCatenaryRingOfField.{u, u} k inferInstance)))) Z
      (X.hom.relativeDimensionFunction (fun _ ↦ 0))
      (dimension (Over.mk (Z.subschemeι ≫ X.hom)) : ℤ))

/-- The cycle of a closed subvariety is its associated cycle in the intrinsic
dimension. -/
theorem subvarietyCycle_def (X : SchemeOverField k) [Variety X]
    (Z : X.left.IdealSheafData) [Variety (Over.mk (Z.subschemeι ≫ X.hom))] :
    subvarietyCycle X Z =
      CycleGroup.toAlgebraicCycle (X.hom.relativeDimensionFunction (fun _ ↦ 0))
        (dimension (Over.mk (Z.subschemeι ≫ X.hom)) : ℤ)
        (@Scheme.IdealSheafData.associatedCycle X.left
          (@LocallyOfFiniteType.isLocallyNoetherian X.left _ X.hom inferInstance
            (@UniversallyCatenary.toIsLocallyNoetherian _
              (@instUniversallyCatenarySpec.{u} k inferInstance
                (@instUniversallyCatenaryRingOfField.{u, u} k inferInstance)))) Z
          (X.hom.relativeDimensionFunction (fun _ ↦ 0))
          (dimension (Over.mk (Z.subschemeι ≫ X.hom)) : ℤ)) := sorry

/-- Proper intersection of two closed subvarieties implies proper intersection of their
canonical algebraic cycles. -/
theorem subvarietyCycles_intersectProperly (X : SchemeOverField k) [Variety X]
    (U V : X.left.IdealSheafData)
    [Variety (Over.mk (U.subschemeι ≫ X.hom))]
    [Variety (Over.mk (V.subschemeι ≫ X.hom))]
    (hUV : TopologicalSpace.Closeds.IntersectProperly U.support V.support) :
    AlgebraicCycle.IntersectProperly (subvarietyCycle X U) (subvarietyCycle X V) := sorry

end AlgebraicGeometry.SchemeOverField
