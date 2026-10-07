module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections.Linear
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.Perfect

/-- The `R`-linear structure on perfect derived modules induced by a morphism to `Spec R`. -/
@[reducible]
noncomputable def linearFor {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) :
    Linear R (RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace)) :=
  @Linear.fullSubcategory (RingedSpace.ModuleDerived X.toRingedSpace) _ _ R _
    (@DerivedCategory.instLinear R _ X.toRingedSpace.Modules _ _
      (Linear.ofRingMorphism
        ((RingedSpace.GlobalSections.centerHom X.toRingedSpace).comp
          (Scheme.Hom.globalSectionsMap f))) _)
    (RingedSpace.ModuleDerived.perfect (X := X.toRingedSpace))

/-- A functor between perfect derived categories is linear for the scalar actions induced by the
two displayed structure morphisms. -/
def IsLinearFor {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    (F : RingedSpace.ModuleDerived.Perfect (X := X.toRingedSpace) ⥤
      RingedSpace.ModuleDerived.Perfect (X := Y.toRingedSpace)) : Prop :=
  @Functor.Linear R _ _ _ _ _ _ _ (linearFor f) (linearFor g) F

end AlgebraicGeometry.Scheme.ModuleDerived.Perfect
