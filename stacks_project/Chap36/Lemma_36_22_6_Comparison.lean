module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.BaseChange.InternalHom

open AlgebraicGeometry CategoryTheory

universe u

#check
  (AlgebraicGeometry.Scheme.Hom.DerivedBaseChange.InternalHom.map :
    ∀ {X X' S S' : Scheme.{u}}
      {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
      [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.TensorDescends X.toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.IsLocalization X.toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X'.toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.TensorDescends X'.toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.IsLocalization X'.toRingedSpace]
      [(RingedSpace.modulePullbackDerived g'.toShHom).Monoidal]
      [RingedSite.Hom.DerivedAdjunction.HasPair
        (RingedSpace.opensRingedSiteHom f.toShHom)]
      [RingedSite.Hom.DerivedAdjunction.HasPair
        (RingedSpace.opensRingedSiteHom f'.toShHom)]
      [IsIso (RingedSpace.modulePullbackDerived.compComparison
        f'.toShHom g.toShHom)]
      [IsIso (RingedSpace.modulePullbackDerived.compComparison
        g'.toShHom f.toShHom)]
      (sq : CommSq g' f' f g)
      (H_X : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
      (H_X' : MonoidalClosed (RingedSpace.ModuleDerived X'.toRingedSpace))
      (M K : RingedSpace.ModuleDerived X.toRingedSpace),
      (RingedSpace.Hom.DerivedBaseChange.source f.toShHom g.toShHom).obj
          ((H_X.ihomOf M).obj K) ⟶
        (RingedSpace.moduleDerivedPushforward f'.toShHom).obj
          ((H_X'.ihomOf
            ((RingedSpace.modulePullbackDerived g'.toShHom).obj M)).obj
            ((RingedSpace.modulePullbackDerived g'.toShHom).obj K)))

#check
  (AlgebraicGeometry.Scheme.Hom.DerivedBaseChange.InternalHom.map_spec :
    ∀ {X X' S S' : Scheme.{u}}
      {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
      [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.TensorDescends X.toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.IsLocalization X.toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X'.toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.TensorDescends X'.toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.IsLocalization X'.toRingedSpace]
      [(RingedSpace.modulePullbackDerived g'.toShHom).Monoidal]
      [RingedSite.Hom.DerivedAdjunction.HasPair
        (RingedSpace.opensRingedSiteHom f.toShHom)]
      [RingedSite.Hom.DerivedAdjunction.HasPair
        (RingedSpace.opensRingedSiteHom f'.toShHom)]
      [IsIso (RingedSpace.modulePullbackDerived.compComparison
        f'.toShHom g.toShHom)]
      [IsIso (RingedSpace.modulePullbackDerived.compComparison
        g'.toShHom f.toShHom)]
      (sq : CommSq g' f' f g)
      (H_X : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
      (H_X' : MonoidalClosed (RingedSpace.ModuleDerived X'.toRingedSpace))
      (M K : RingedSpace.ModuleDerived X.toRingedSpace),
      AlgebraicGeometry.Scheme.Hom.DerivedBaseChange.InternalHom.map
          sq H_X H_X' M K =
        (AlgebraicGeometry.Scheme.Hom.DerivedBaseChange.map sq).app
            ((H_X.ihomOf M).obj K) ≫
          (RingedSpace.moduleDerivedPushforward f'.toShHom).map
            (Functor.PullbackInternalHom.comparisonOf H_X H_X'
              (RingedSpace.modulePullbackDerived g'.toShHom)
              (fun A B ↦ (Functor.Monoidal.μIso
                (RingedSpace.modulePullbackDerived g'.toShHom) A B).symm)
              M K))
