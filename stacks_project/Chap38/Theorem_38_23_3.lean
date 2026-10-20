module

public import ReasLib.AlgebraicGeometry.Scheme.Module.BaseChange.IsomorphismFunctor.ClosedImmersion
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Theorem 38.23.3 (1): the isomorphism functor of a surjective map from a finitely
presented module that is flat and pure over the base is represented by a closed immersion. -/
@[stacks 05PF] #check
  (AlgebraicGeometry.Scheme.Modules.IsomorphismFunctor.exists_closedImmersion_representation :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.Scheme.Hom.FinitePresentation f] (ℱ 𝒢 : X.Modules)
      [ℱ.IsFinitePresentation] [𝒢.IsQuasicoherent]
      [SheafOfModules.IsFlatOver ℱ f.toShHom]
      (h_pure : AlgebraicGeometry.Scheme.Modules.IsPureOver ℱ f)
      (u : ℱ ⟶ 𝒢) [Epi u],
      ∃ Z : Over S,
        Nonempty ((AlgebraicGeometry.Scheme.Modules.isomorphismFunctor f u).RepresentableBy Z) ∧
          AlgebraicGeometry.IsClosedImmersion Z.hom)

/- Theorem 38.23.3 (2): if the target module is also finitely presented, the closed
immersion representing the isomorphism functor can be chosen finitely presented. -/
@[stacks 05PF] #check
  (AlgebraicGeometry.Scheme.Modules.IsomorphismFunctor.exists_closedImmersion_representation_of_finitePresentation :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.Scheme.Hom.FinitePresentation f] (ℱ 𝒢 : X.Modules)
      [ℱ.IsFinitePresentation] [𝒢.IsFinitePresentation]
      [SheafOfModules.IsFlatOver ℱ f.toShHom]
      (h_pure : AlgebraicGeometry.Scheme.Modules.IsPureOver ℱ f)
      (u : ℱ ⟶ 𝒢) [Epi u],
      ∃ Z : Over S,
        Nonempty ((AlgebraicGeometry.Scheme.Modules.isomorphismFunctor f u).RepresentableBy Z) ∧
          AlgebraicGeometry.IsClosedImmersion Z.hom ∧
            AlgebraicGeometry.Scheme.Hom.FinitePresentation Z.hom)
