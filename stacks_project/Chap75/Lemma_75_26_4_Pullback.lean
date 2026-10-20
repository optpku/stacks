module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback
public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.Preadditive
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Basic

/-!
# Derived pullback of modules along morphisms of algebraic spaces

An arbitrary morphism of algebraic spaces induces the unbounded derived inverse image
`Lf^*` as the total left derived functor of module pullback. Étale morphisms already have
an exact derived pullback; the two agree up to isomorphism.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.ModuleQis :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    MorphismProperty (HomotopyCategory (Modules X) (up ℤ)))

#check (AlgebraicGeometry.AlgebraicSpace.modulePullbackToDerived :
  ∀ {S : Scheme.{u}} {Y X : AlgebraicSpace S} (f : Y ⟶ X),
    HomotopyCategory (Modules X) (up ℤ) ⥤ ModuleDerived Y)

#check (AlgebraicGeometry.AlgebraicSpace.instModulePullbackToDerivedHasLeftDerivedFunctor :
  ∀ {S : Scheme.{u}} {Y X : AlgebraicSpace S} (f : Y ⟶ X),
    (modulePullbackToDerived f).HasLeftDerivedFunctor (ModuleQis X))

#check (AlgebraicGeometry.AlgebraicSpace.modulePullbackDerived :
  ∀ {S : Scheme.{u}} {Y X : AlgebraicSpace S} (f : Y ⟶ X),
    ModuleDerived X ⥤ ModuleDerived Y)

#check (AlgebraicGeometry.AlgebraicSpace.modulePullbackDerived_eq :
  ∀ {S : Scheme.{u}} {Y X : AlgebraicSpace S} (f : Y ⟶ X),
    modulePullbackDerived f =
      (modulePullbackToDerived f).totalLeftDerived DerivedCategory.Qh (ModuleQis X))

/- The concrete derived pullback is canonically isomorphic to the total left derived
functor of module pullback. -/
#check (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.pullbackIsoTotalLeftDerived :
  ∀ {S : Scheme.{u}} {Y X : AlgebraicSpace S} (f : Y ⟶ X),
    ModuleDerived.pullback f ≅ Functor.LeftDerived.Homotopy.functor (Modules.pullback f))

end AlgebraicGeometry.AlgebraicSpace
