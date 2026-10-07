module

public import ReasLib.Algebra.Category.ModuleCat.IdealPower.Torsion
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.CategoryTheory.Adjunction.Derived.Unbounded

/-!
# Derived ideal-power torsion

The primary-component coreflector admits a K-injective total right-derived functor, which is
right adjoint to the derived inclusion of ideal-power-torsion modules.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.IdealPowerTorsion

variable {A : Type u} [CommRing A]

/-- Ideal-power-torsion modules use the standard unbounded derived-category model. -/
@[reducible, instance]
noncomputable def hasDerivedCategory (I : Ideal A) : HasDerivedCategory (category I) :=
  HasDerivedCategory.standard (category I)

/-- The derived inclusion of ideal-power-torsion modules. -/
noncomputable abbrev derivedInclusion (I : Ideal A) :
    DerivedCategory (category I) ⥤ DerivedCategory (ModuleCat.{u} A) :=
  (exactInclusion I).obj.mapDerivedCategory

/-- The K-injective total right-derived primary-component functor `RΓ_I`. -/
noncomputable abbrev derivedTorsion (I : Ideal A) :
    DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (category I) :=
  Functor.RightDerived.KInjective.functor (coreflector I)

/-- The derived inclusion is left adjoint to the total right-derived primary-component
functor. -/
noncomputable def derivedAdjunction (I : Ideal A) :
    derivedInclusion I ⊣ derivedTorsion I :=
  CategoryTheory.Adjunction.Derived.KInjective.adjunction
    (exactInclusion I) (coreflector I) (adjunction I)

/-- For a finitely generated ideal, the derived inclusion is left adjoint to the total
right-derived primary-component functor. -/
noncomputable def derivedAdjunctionOfFG (I : Ideal A) (_ : I.FG) :
    derivedInclusion I ⊣ derivedTorsion I :=
  derivedAdjunction I

/-- The total right-derived primary-component functor is canonically a right adjoint. -/
instance derivedTorsionIsRightAdjoint (I : Ideal A) :
    (derivedTorsion I).IsRightAdjoint := sorry

/-- The Hom equivalence induced by the derived ideal-power-torsion adjunction. -/
noncomputable def homEquiv (I : Ideal A)
    (K : DerivedCategory (category I)) (L : DerivedCategory (ModuleCat.{u} A)) :
    ((derivedInclusion I).obj K ⟶ L) ≃ (K ⟶ (derivedTorsion I).obj L) :=
  (derivedAdjunction I).homEquiv K L

end CategoryTheory.ModuleCat.IdealPowerTorsion

end
