module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Sheaf
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v w x

/-!
# Definition 34.9.13

This chapter entry is a compatibility facade for generic family sheafness and
the canonical fpqc sheaf condition.
-/

/- Definition 34.9.13: a scheme presheaf satisfies the sheaf property for a
fixed-target family when compatible sections glue uniquely. -/
@[stacks 022G] #check
  (AlgebraicGeometry.satisfiesSheafPropertyForFamily :
    ∀ (F : AlgebraicGeometry.Scheme.{u}ᵒᵖ ⥤ Type v)
      {ι : Type w} {T : AlgebraicGeometry.Scheme.{u}},
      (family : ι → AlgebraicGeometry.Scheme.{u}) →
        (map : ∀ i, family i ⟶ T) → Prop)

#check
  (AlgebraicGeometry.satisfiesSheafPropertyForFamily_iff :
    ∀ (F : AlgebraicGeometry.Scheme.{u}ᵒᵖ ⥤ Type v)
      {ι : Type w} {T : AlgebraicGeometry.Scheme.{u}}
      (family : ι → AlgebraicGeometry.Scheme.{u}) (map : ∀ i, family i ⟶ T),
      AlgebraicGeometry.satisfiesSheafPropertyForFamily F family map ↔
        CategoryTheory.Presieve.IsSheafFor F
          (CategoryTheory.Presieve.ofArrows family map))

#check
  (CategoryTheory.Presheaf.IsSheafForFamily :
    ∀ {C : Type u} [Category.{v} C] (F : Cᵒᵖ ⥤ Type w)
      {ι : Type x} {T : C},
      (family : ι → C) → (map : ∀ i, family i ⟶ T) → Prop)

#check
  (CategoryTheory.Presheaf.isSheafForFamily_iff :
    ∀ {C : Type u} [Category.{v} C] (F : Cᵒᵖ ⥤ Type w)
      {ι : Type x} {T : C} (family : ι → C) (map : ∀ i, family i ⟶ T),
      CategoryTheory.Presheaf.IsSheafForFamily F family map ↔
        CategoryTheory.Presieve.IsSheafFor F
          (CategoryTheory.Presieve.ofArrows family map))

#check
  (AlgebraicGeometry.satisfiesFpqcSheafProperty :
    (F : AlgebraicGeometry.Scheme.{u}ᵒᵖ ⥤ Type v) → Prop)

#check
  (AlgebraicGeometry.satisfiesFpqcSheafProperty_iff :
    ∀ (F : AlgebraicGeometry.Scheme.{u}ᵒᵖ ⥤ Type v),
      AlgebraicGeometry.satisfiesFpqcSheafProperty F ↔
        CategoryTheory.Presheaf.IsSheaf AlgebraicGeometry.Scheme.fpqcTopology F)

#check
  (AlgebraicGeometry.satisfiesZariskiSheafProperty :
    (F : AlgebraicGeometry.Scheme.{u}ᵒᵖ ⥤ Type v) → Prop)

#check
  (AlgebraicGeometry.satisfiesZariskiSheafProperty_iff :
    ∀ (F : AlgebraicGeometry.Scheme.{u}ᵒᵖ ⥤ Type v),
      AlgebraicGeometry.satisfiesZariskiSheafProperty F ↔
        CategoryTheory.Presheaf.IsSheaf AlgebraicGeometry.Scheme.zariskiTopology F)
