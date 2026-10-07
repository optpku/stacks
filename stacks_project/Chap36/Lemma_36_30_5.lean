module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Pushforward.FlatCoefficients

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme.Hom
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived

/- Lemma 36.30.5 (1): the derived pushforward of a pseudo-coherent complex along a flat,
proper morphism of finite presentation is pseudo-coherent. -/
@[stacks 0CSD] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.pushforward_isPseudoCoherent_of_isPseudoCoherent :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      [Flat f] [IsProper f] [Scheme.Hom.FinitePresentation f]
      (E : RingedSpace.ModuleDerived X.toRingedSpace)
      (_ : RingedSpace.ModuleDerived.IsPseudoCoherent E),
      RingedSpace.ModuleDerived.IsPseudoCoherent
        ((RingedSpace.moduleDerivedPushforward f.toShHom).obj E))

/- Lemma 36.30.5 (2): for a pseudo-coherent complex and any cartesian base-change square,
the canonical derived base-change component for its pushforward is invertible. -/
@[stacks 0CSD] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.pushforward_baseChange_isIso_of_isPseudoCoherent :
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
      (_ : RingedSpace.ModuleDerived.IsPseudoCoherent E),
      IsIso ((Scheme.Hom.DerivedBaseChange.map sq.toCommSq).app E))

end AlgebraicGeometry.Scheme.ModuleDerived
