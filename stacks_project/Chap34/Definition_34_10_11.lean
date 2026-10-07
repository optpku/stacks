module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Cover.V.SheafCondition

@[expose] public section

open CategoryTheory

universe u v w

/- Definition 34.10.11: a contravariant set-valued functor on schemes has
the sheaf property for the `V` topology when it has the fixed-family sheaf
property for every `V` covering. -/
@[stacks 0ETL] #check
  (AlgebraicGeometry.satisfiesVSheafProperty.{u, v, w} :
    (AlgebraicGeometry.Scheme.{u}ᵒᵖ ⥤ Type v) → Prop)

#check
  (AlgebraicGeometry.satisfiesVSheafProperty.isSheafFor.{u, v, w} :
    ∀ {F : AlgebraicGeometry.Scheme.{u}ᵒᵖ ⥤ Type v}
      (hF : AlgebraicGeometry.satisfiesVSheafProperty.{u, v, w} F)
      {ι : Type w} {T : AlgebraicGeometry.Scheme.{u}}
      (family : ι → AlgebraicGeometry.Scheme.{u})
      (map : ∀ i, family i ⟶ T),
        AlgebraicGeometry.IsVCovering T family map →
          AlgebraicGeometry.satisfiesSheafPropertyForFamily F family map)

#check
  (AlgebraicGeometry.satisfiesVSheafProperty_iff.{u, v, w} :
    ∀ F : AlgebraicGeometry.Scheme.{u}ᵒᵖ ⥤ Type v,
      AlgebraicGeometry.satisfiesVSheafProperty.{u, v, w} F ↔
        ∀ {ι : Type w} {T : AlgebraicGeometry.Scheme.{u}}
          (family : ι → AlgebraicGeometry.Scheme.{u})
          (map : ∀ i, family i ⟶ T),
            AlgebraicGeometry.IsVCovering T family map →
              AlgebraicGeometry.satisfiesSheafPropertyForFamily F family map)
