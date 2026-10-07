module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.AssociatedCycle.Variety

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

#check
  (AlgebraicGeometry.SchemeOverField.subvarietyCycle :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) [Variety X]
      (Z : X.left.IdealSheafData) [Variety (Over.mk (Z.subschemeι ≫ X.hom))],
      AlgebraicGeometry.AlgebraicCycle X.left ℤ)

#check
  (AlgebraicGeometry.SchemeOverField.subvarietyCycle_def :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) [Variety X]
      (Z : X.left.IdealSheafData) [Variety (Over.mk (Z.subschemeι ≫ X.hom))],
      AlgebraicGeometry.SchemeOverField.subvarietyCycle X Z =
        AlgebraicGeometry.CycleGroup.toAlgebraicCycle
          (X.hom.relativeDimensionFunction (fun _ ↦ 0))
          (AlgebraicGeometry.SchemeOverField.dimension
            (Over.mk (Z.subschemeι ≫ X.hom)) : ℤ)
          (@AlgebraicGeometry.Scheme.IdealSheafData.associatedCycle X.left
            (@AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian X.left _ X.hom
              inferInstance
              (@AlgebraicGeometry.UniversallyCatenary.toIsLocallyNoetherian _
                (@AlgebraicGeometry.instUniversallyCatenarySpec.{u} k inferInstance
                  (@instUniversallyCatenaryRingOfField.{u, u} k inferInstance)))) Z
            (X.hom.relativeDimensionFunction (fun _ ↦ 0))
            (AlgebraicGeometry.SchemeOverField.dimension
              (Over.mk (Z.subschemeι ≫ X.hom)) : ℤ)))

#check
  (AlgebraicGeometry.SchemeOverField.subvarietyCycles_intersectProperly :
    ∀ {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) [Variety X]
      (U V : X.left.IdealSheafData)
      [Variety (Over.mk (U.subschemeι ≫ X.hom))]
      [Variety (Over.mk (V.subschemeι ≫ X.hom))],
      TopologicalSpace.Closeds.IntersectProperly U.support V.support →
        AlgebraicGeometry.AlgebraicCycle.IntersectProperly
          (AlgebraicGeometry.SchemeOverField.subvarietyCycle X U)
          (AlgebraicGeometry.SchemeOverField.subvarietyCycle X V))
