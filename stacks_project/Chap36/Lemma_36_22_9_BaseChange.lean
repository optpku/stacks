/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.BaseChange

open AlgebraicGeometry CategoryTheory

universe u

#check
  (AlgebraicGeometry.Scheme.Hom.DerivedBaseChange.map :
    ∀ {X X' S S' : Scheme.{u}}
      {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom f.toShHom)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom f'.toShHom)]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison f'.toShHom g.toShHom)]
    [IsIso (RingedSpace.modulePullbackDerived.compComparison g'.toShHom f.toShHom)]
    (sq : CommSq g' f' f g),
    RingedSpace.Hom.DerivedBaseChange.source f.toShHom g.toShHom ⟶
      RingedSpace.Hom.DerivedBaseChange.target g'.toShHom f'.toShHom)

#check
  (AlgebraicGeometry.Scheme.Hom.DerivedBaseChange.map_isMap :
    ∀ {X X' S S' : Scheme.{u}}
      {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom f.toShHom)]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom f'.toShHom)]
    [hleft : IsIso
      (RingedSpace.modulePullbackDerived.compComparison f'.toShHom g.toShHom)]
    [hright : IsIso
      (RingedSpace.modulePullbackDerived.compComparison g'.toShHom f.toShHom)]
    (sq : CommSq g' f' f g),
    RingedSpace.Hom.DerivedBaseChange.IsMap
      (RingedSpace.modulePullbackDerivedPushforwardAdjunction f.toShHom)
      (RingedSpace.modulePullbackDerivedPushforwardAdjunction f'.toShHom)
      (@RingedSpace.Hom.DerivedBaseChange.pullbackIsoOfIsIso _ _ _ _
        g'.toShHom f'.toShHom f.toShHom g.toShHom
        ((sq.map (Scheme.forgetToLocallyRingedSpace ⋙
          LocallyRingedSpace.forgetToSheafedSpace)) :
            CommSq g'.toShHom f'.toShHom f.toShHom g.toShHom)
        hleft hright)
      (AlgebraicGeometry.Scheme.Hom.DerivedBaseChange.map sq))
