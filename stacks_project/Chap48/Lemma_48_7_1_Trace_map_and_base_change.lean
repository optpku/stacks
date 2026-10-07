module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.BaseChange.Trace
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- Lemma 48.7.1 (Trace map and base change): for a Tor-independent cartesian square
of quasi-compact and quasi-separated schemes, the canonical base-change map followed by
its inverse mate and the counit for `f'` equals the pullback of the counit for `f`. -/
@[stacks 0B6J] #check
  (@AlgebraicGeometry.Scheme.DerivedQCoh.BaseChange.map_app_comp_counit :
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
        Scheme.DerivedQCoh.BaseChange.map g' f' f g sq.toCommSq)
      (K : Scheme.DerivedQCoh Y),
      (Scheme.DerivedQCoh.BaseChange.map g' f' f g sq.toCommSq).app (a.obj K) ≫
          (Scheme.DerivedQCoh.pushforwardCohomologyIn f').map
            ((CategoryTheory.DerivedBaseChange.map fAdj f'Adj baseChangeIso.symm).app K) ≫
        f'Adj.counit.app ((Scheme.DerivedQCoh.pullback g).obj K) =
      (Scheme.DerivedQCoh.pullback g).map (fAdj.counit.app K))
