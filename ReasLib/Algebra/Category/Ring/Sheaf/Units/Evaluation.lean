module

public import ReasLib.Algebra.Category.Ring.Sheaf.Units.Map
public import Mathlib.Topology.Sheaves.Abelian

/-!
# Units evaluation differences

Multiplicative evaluation differences represented in the additive units sheaf.
-/

@[expose] public section

open CategoryTheory TopCat TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The multiplicative difference of two morphisms into a common sheaf of commutative rings. -/
noncomputable abbrev unitsEvaluationDifference {X : TopCat.{u}}
    {A B : X.Sheaf CommRingCat.{u}} (evalA evalB : A ⟶ B) :
    CategoryTheory.Sheaf.unitsAddSheaf A ⟶ CategoryTheory.Sheaf.unitsAddSheaf B :=
  CategoryTheory.Sheaf.unitsAddMap evalA +
    (-CategoryTheory.Sheaf.unitsAddMap evalB)

/-- On sections, a units evaluation difference is the product with the inverse value. -/
theorem unitsEvaluationDifference_app {X : TopCat.{u}}
    {A B : X.Sheaf CommRingCat.{u}} (evalA evalB : A ⟶ B)
    (U : (Opens X)ᵒᵖ) (h : (CategoryTheory.Sheaf.unitsAddSheaf A).1.obj U) :
    CategoryTheory.Sheaf.unitsAddSheafUnit B
        ((unitsEvaluationDifference evalA evalB).hom.app U h) =
      Units.map (evalA.hom.app U).hom.toMonoidHom
          (CategoryTheory.Sheaf.unitsAddSheafUnit A h) *
        (Units.map (evalB.hom.app U).hom.toMonoidHom
          (CategoryTheory.Sheaf.unitsAddSheafUnit A h))⁻¹ := sorry

end AlgebraicGeometry
