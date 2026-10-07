module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.BaseChange.Trace
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- Lemma 48.7.2: for a Tor-independent cartesian square of quasi-compact and
quasi-separated schemes, the adjunction units commute with the canonical base-change
transformation and its inverse mate. -/
@[stacks 0B6K] #check
  (@AlgebraicGeometry.Scheme.DerivedQCoh.BaseChange.unit_baseChange :
    ∀ {X' X Y' Y : Scheme.{u}}
      [CompactSpace X'] [QuasiSeparatedSpace X']
      [CompactSpace X] [QuasiSeparatedSpace X]
      [CompactSpace Y'] [QuasiSeparatedSpace Y']
      [CompactSpace Y] [QuasiSeparatedSpace Y]
      (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
      (sq : IsPullback g' f' f g)
      (a : Scheme.DerivedQCoh Y ⥤ Scheme.DerivedQCoh X)
      (a' : Scheme.DerivedQCoh Y' ⥤ Scheme.DerivedQCoh X')
      (fAdj : Scheme.DerivedQCoh.pushforwardCohomologyIn f ⊣ a)
      (f'Adj : Scheme.DerivedQCoh.pushforwardCohomologyIn f' ⊣ a')
      (hTor : Scheme.TorIndependentOver (Over.mk f) (Over.mk g))
      (baseChangeIso :
        Scheme.DerivedQCoh.pushforwardCohomologyIn f ⋙ Scheme.DerivedQCoh.pullback g ≅
          Scheme.DerivedQCoh.pullback g' ⋙
            Scheme.DerivedQCoh.pushforwardCohomologyIn f')
      (h_baseChange : baseChangeIso.hom =
        Scheme.DerivedQCoh.BaseChange.map g' f' f g sq.toCommSq),
      (Scheme.DerivedQCoh.pullback g').leftUnitor.inv ≫
            Functor.whiskerRight fAdj.unit (Scheme.DerivedQCoh.pullback g') ≫
            (Functor.associator (Scheme.DerivedQCoh.pushforwardCohomologyIn f) a
              (Scheme.DerivedQCoh.pullback g')).hom ≫
            Functor.whiskerLeft (Scheme.DerivedQCoh.pushforwardCohomologyIn f)
              (CategoryTheory.DerivedBaseChange.map fAdj f'Adj baseChangeIso.symm) ≫
            (Functor.associator (Scheme.DerivedQCoh.pushforwardCohomologyIn f)
              (Scheme.DerivedQCoh.pullback g) a').inv ≫
          Functor.whiskerRight
            (Scheme.DerivedQCoh.BaseChange.map g' f' f g sq.toCommSq) a' =
        (Scheme.DerivedQCoh.pullback g').rightUnitor.inv ≫
            Functor.whiskerLeft (Scheme.DerivedQCoh.pullback g') f'Adj.unit ≫
          (Functor.associator (Scheme.DerivedQCoh.pullback g')
            (Scheme.DerivedQCoh.pushforwardCohomologyIn f') a').inv)
