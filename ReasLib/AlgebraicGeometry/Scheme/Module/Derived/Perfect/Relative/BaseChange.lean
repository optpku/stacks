module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Relative
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

namespace AlgebraicGeometry.Scheme.ModuleDerived.IsPerfectRelativeTo

/-- Derived pullback along a base change preserves relative perfectness over a flat,
locally finitely presented morphism of schemes. -/
theorem baseChange {X S S' : Scheme.{u}}
    (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (g : S' ⟶ S)
    [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase f.toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase f.toShHom).restrict U.isOpenEmbedding))]
    [∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase (pullback.snd f g).toShHom).carrier,
      DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules
          ((RingedSpace.Hom.inverseImageBase (pullback.snd f g).toShHom).restrict U.isOpenEmbedding))] (K : RingedSpace.ModuleDerived X.toRingedSpace)
    (hK : IsPerfectRelativeTo f K) :
    IsPerfectRelativeTo (pullback.snd f g)
      ((RingedSpace.modulePullbackDerived (pullback.fst f g).toShHom).obj K) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.IsPerfectRelativeTo
