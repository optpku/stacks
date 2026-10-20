module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.PresentationRestriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.EtalePullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HigherDirectImage.EtaleBaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Basic

/-! # Derived restriction of modules along étale morphisms

Étale restriction of module sheaves is exact and therefore induces a functor on
the unbounded derived categories.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Étale restriction of module sheaves preserves finite limits. -/
instance restrictFunctor_preservesFiniteLimits (f : X ⟶ Y) [Etale f] :
    PreservesFiniteLimits (restrictFunctor f) :=
  sorry

/-- Étale restriction of module sheaves preserves finite colimits. -/
instance restrictFunctor_preservesFiniteColimits (f : X ⟶ Y) [Etale f] :
    PreservesFiniteColimits (restrictFunctor f) :=
  sorry

/-- The functor induced on unbounded derived module categories by étale restriction. -/
abbrev restrictFunctorDerived (f : X ⟶ Y) [Etale f] :
    ModuleDerived Y ⥤ ModuleDerived X :=
  @Functor.mapDerivedCategory Y.Modules _ Y.modulesAbelian (modulesHasDerivedCategory Y)
    X.Modules _ X.modulesAbelian (modulesHasDerivedCategory X) (restrictFunctor f)
    inferInstance inferInstance inferInstance

/-- The derived restriction functor is the canonical functor induced by the underived one. -/
theorem restrictFunctorDerived_eq (f : X ⟶ Y) [Etale f] :
    restrictFunctorDerived f =
      @Functor.mapDerivedCategory Y.Modules _ Y.modulesAbelian (modulesHasDerivedCategory Y)
        X.Modules _ X.modulesAbelian (modulesHasDerivedCategory X) (restrictFunctor f)
        inferInstance inferInstance inferInstance :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Modules

