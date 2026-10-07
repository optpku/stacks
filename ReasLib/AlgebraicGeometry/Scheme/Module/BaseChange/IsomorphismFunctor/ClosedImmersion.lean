module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Purity
public import ReasLib.AlgebraicGeometry.Scheme.Module.BaseChange.IsomorphismFunctor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation

/-!
# Closed representability of the module isomorphism functor

This module records when the isomorphism functor of a morphism of scheme modules is represented
by a closed subscheme of the base.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules.IsomorphismFunctor

/-- The isomorphism functor of an epimorphism from a finitely presented module that is flat and
pure over the base is represented by a closed immersion. -/
theorem exists_closedImmersion_representation {X S : Scheme.{u}} (f : X ⟶ S)
    [Scheme.Hom.FinitePresentation f] (ℱ 𝒢 : X.Modules)
    [ℱ.IsFinitePresentation] [𝒢.IsQuasicoherent]
    [SheafOfModules.IsFlatOver ℱ f.toShHom] (h_pure : ℱ.IsPureOver f)
    (u : ℱ ⟶ 𝒢) [Epi u] :
    ∃ Z : Over S, Nonempty ((Scheme.Modules.isomorphismFunctor f u).RepresentableBy Z) ∧
      IsClosedImmersion Z.hom := sorry

/-- If the target module is finitely presented, the closed immersion representing the
isomorphism functor can also be chosen finitely presented. -/
theorem exists_closedImmersion_representation_of_finitePresentation
    {X S : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.FinitePresentation f]
    (ℱ 𝒢 : X.Modules) [ℱ.IsFinitePresentation] [𝒢.IsFinitePresentation]
    [SheafOfModules.IsFlatOver ℱ f.toShHom] (h_pure : ℱ.IsPureOver f)
    (u : ℱ ⟶ 𝒢) [Epi u] :
    ∃ Z : Over S, Nonempty ((Scheme.Modules.isomorphismFunctor f u).RepresentableBy Z) ∧
      IsClosedImmersion Z.hom ∧ Scheme.Hom.FinitePresentation Z.hom := sorry

end AlgebraicGeometry.Scheme.Modules.IsomorphismFunctor
