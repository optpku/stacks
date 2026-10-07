module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import stacks_project.Chap69.«69_3_0_1_Comparison»
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh

/-!
# Derived étale restriction of modules on algebraic spaces

Étale restriction of `𝒪`-modules is exact, so it induces a functor on unbounded derived
categories `D(𝒪_Y) ⥤ D(𝒪_X)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Restriction of modules along an étale morphism of algebraic spaces preserves finite limits. -/
instance restrictFunctor_preservesFiniteLimits (f : X ⟶ Y) [Etale f] :
    PreservesFiniteLimits (restrictFunctor f) :=
  sorry

/-- Restriction of modules along an étale morphism of algebraic spaces preserves finite
colimits. -/
instance restrictFunctor_preservesFiniteColimits (f : X ⟶ Y) [Etale f] :
    PreservesFiniteColimits (restrictFunctor f) :=
  sorry

/-- The derived étale restriction functor `(-)|_X : D(𝒪_Y) ⥤ D(𝒪_X)`. -/
abbrev restrictFunctorDerived (f : X ⟶ Y) [Etale f]
    [(restrictFunctor f).Additive]
    [PreservesFiniteLimits (restrictFunctor f)]
    [PreservesFiniteColimits (restrictFunctor f)] :
    ModuleDerived Y ⥤ ModuleDerived X :=
  @Functor.mapDerivedCategory Y.Modules _ Y.modulesAbelian (modulesHasDerivedCategory Y)
    X.Modules _ X.modulesAbelian (modulesHasDerivedCategory X) (restrictFunctor f)
    inferInstance inferInstance inferInstance

/-- Derived étale restriction is `mapDerivedCategory` of underived étale restriction. -/
theorem restrictFunctorDerived_eq (f : X ⟶ Y) [Etale f]
    [(restrictFunctor f).Additive]
    [PreservesFiniteLimits (restrictFunctor f)]
    [PreservesFiniteColimits (restrictFunctor f)] :
    restrictFunctorDerived f =
      @Functor.mapDerivedCategory Y.Modules _ Y.modulesAbelian (modulesHasDerivedCategory Y)
        X.Modules _ X.modulesAbelian (modulesHasDerivedCategory X) (restrictFunctor f)
        inferInstance inferInstance inferInstance :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Modules
