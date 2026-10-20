module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.Perfect.Tensor

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme.Hom
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived

/-- The derived pushforward of a perfect complex along a flat, proper morphism of finite
presentation is perfect. -/
theorem pushforward_isPerfect_of_isPerfect {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [Scheme.Hom.FinitePresentation f]
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPerfect E) :
    RingedSpace.ModuleDerived.IsPerfect
      ((RingedSpace.moduleDerivedPushforward f.toShHom).obj E) := sorry

/-- For a perfect complex and any cartesian base-change square, the canonical derived
base-change component for its pushforward is invertible. -/
theorem pushforward_baseChange_isIso_of_isPerfect
    {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    [Flat f] [IsProper f] [Scheme.Hom.FinitePresentation f]
    [HasPair (RingedSpace.opensRingedSiteHom f.toShHom)]
    [HasPair (RingedSpace.opensRingedSiteHom f'.toShHom)]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison f'.toShHom g.toShHom)]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison g'.toShHom f.toShHom)]
    (sq : IsPullback g' f' f g)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPerfect E) :
    IsIso ((DerivedBaseChange.map sq.toCommSq).app E) := sorry

/-- If an `𝒪_X`-module is finitely presented and flat over the base, its degree-zero derived
pushforward along a proper morphism of finite presentation is perfect. -/
theorem pushforward_single_isPerfect_of_finitePresentation
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [Scheme.Hom.FinitePresentation f]
    (G : X.Modules) [G.IsFinitePresentation]
    [SheafOfModules.IsFlatOver G f.toShHom] :
    RingedSpace.ModuleDerived.IsPerfect
      ((RingedSpace.moduleDerivedPushforward f.toShHom).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj G)) := sorry

/-- For a finitely presented `𝒪_X`-module flat over the base and any cartesian base-change
square, the canonical base-change component for its degree-zero derived pushforward is
invertible. -/
theorem pushforward_single_baseChange_isIso_of_finitePresentation
    {X' X S' S : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
    [IsProper f] [Scheme.Hom.FinitePresentation f]
    [HasPair (RingedSpace.opensRingedSiteHom f.toShHom)]
    [HasPair (RingedSpace.opensRingedSiteHom f'.toShHom)]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison f'.toShHom g.toShHom)]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison g'.toShHom f.toShHom)]
    (sq : IsPullback g' f' f g)
    (G : X.Modules) [G.IsFinitePresentation]
    [SheafOfModules.IsFlatOver G f.toShHom] :
    IsIso ((DerivedBaseChange.map sq.toCommSq).app
      ((DerivedCategory.singleFunctor X.Modules 0).obj G)) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived
