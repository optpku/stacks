module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.LocalConcentration

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

#check
  (AlgebraicGeometry.RingedSpace.ModuleDerived.IsLocallyConcentrated :
    ∀ {X : RingedSpace.{u}},
      AlgebraicGeometry.RingedSpace.ModuleDerived X → Prop)

#check
  (AlgebraicGeometry.RingedSpace.ModuleDerived.isLocallyConcentrated_iff :
    ∀ {X : RingedSpace.{u}}
      (E : AlgebraicGeometry.RingedSpace.ModuleDerived X),
      AlgebraicGeometry.RingedSpace.ModuleDerived.IsLocallyConcentrated E ↔
        ∀ x : X, ∃ U : Opens X, x ∈ U ∧ ∃ n : ℤ, ∀ y : X, y ∈ U →
          DerivedCategory.concentrated (ModuleCat (X.presheaf.stalk y)) n
            (AlgebraicGeometry.RingedSpace.ModuleDerived.Stalk.obj E y))

#check
  (AlgebraicGeometry.RingedSpace.ModuleDerived.IsLocallyConcentrated.at :
    ∀ {X : RingedSpace.{u}}
      {E : AlgebraicGeometry.RingedSpace.ModuleDerived X},
      AlgebraicGeometry.RingedSpace.ModuleDerived.IsLocallyConcentrated E → ∀ x : X,
        ∃ n : ℤ, DerivedCategory.concentrated (ModuleCat (X.presheaf.stalk x)) n
          (AlgebraicGeometry.RingedSpace.ModuleDerived.Stalk.obj E x))
