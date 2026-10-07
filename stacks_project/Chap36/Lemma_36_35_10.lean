module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.Perfect

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived

/- Lemma 36.35.10 (1): the derived pushforward of an `S`-perfect complex along a flat,
proper morphism of finite presentation is perfect. -/
@[stacks 0DJT] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.pushforward_isPerfect_of_isPerfectRelativeTo :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      [Flat f] [IsProper f] [Scheme.Hom.FinitePresentation f]
      (E : RingedSpace.ModuleDerived X.toRingedSpace)
      (_ : RingedSpace.ModuleDerived.IsPerfectOver f.toShHom E),
      RingedSpace.ModuleDerived.IsPerfect
        ((RingedSpace.moduleDerivedPushforward f.toShHom).obj E))

/- Lemma 36.35.10 (2): for an `S`-perfect complex and any cartesian base-change square,
the canonical derived base-change component for its pushforward is invertible. -/
@[stacks 0DJT] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.pushforward_baseChange_isIso_of_isPerfectRelativeTo :
    ∀ {X' X S' S : Scheme.{u}}
      (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
      [Flat f] [IsProper f] [Scheme.Hom.FinitePresentation f]
      [RingedSite.Hom.DerivedAdjunction.HasPair
        (RingedSpace.opensRingedSiteHom f.toShHom)]
      [RingedSite.Hom.DerivedAdjunction.HasPair
        (RingedSpace.opensRingedSiteHom f'.toShHom)]
      [IsIso (RingedSpace.modulePullbackDerived.compComparison f'.toShHom g.toShHom)]
      [IsIso (RingedSpace.modulePullbackDerived.compComparison g'.toShHom f.toShHom)]
      (sq : IsPullback g' f' f g)
      (E : RingedSpace.ModuleDerived X.toRingedSpace)
      (_ : RingedSpace.ModuleDerived.IsPerfectOver f.toShHom E),
      IsIso ((Scheme.Hom.DerivedBaseChange.map sq.toCommSq).app E))

end AlgebraicGeometry.Scheme.ModuleDerived
