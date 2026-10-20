module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Restriction

/-!
# Derived étale restriction of modules on algebraic spaces

Étale restriction of module sheaves is exact, so it induces a functor on unbounded derived
categories.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits

noncomputable section

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Modules.restrictFunctor_preservesFiniteLimits :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f],
    PreservesFiniteLimits (restrictFunctor f))
#check (AlgebraicGeometry.AlgebraicSpace.Modules.restrictFunctor_preservesFiniteColimits :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f],
    PreservesFiniteColimits (restrictFunctor f))
#check (AlgebraicGeometry.AlgebraicSpace.Modules.restrictFunctorDerived :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f],
    ModuleDerived Y ⥤ ModuleDerived X)
#check (AlgebraicGeometry.AlgebraicSpace.Modules.restrictFunctorDerived_eq :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f],
    restrictFunctorDerived f =
      @Functor.mapDerivedCategory Y.Modules _ Y.modulesAbelian
        (modulesHasDerivedCategory Y) X.Modules _ X.modulesAbelian
        (modulesHasDerivedCategory X) (restrictFunctor f)
        inferInstance inferInstance inferInstance)
