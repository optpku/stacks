/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.BaseChange
public import ReasLib.CategoryTheory.Adjunction.BaseChange

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh.BaseChange

/-- For a Tor-independent cartesian square of quasi-compact and quasi-separated schemes,
the canonical derived base-change map followed by the inverse mate and the target counit
equals the pullback of the source counit. -/
theorem map_app_comp_counit
    {X' X Y' Y : Scheme.{u}}
    [CompactSpace X'] [QuasiSeparatedSpace X']
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y'] [QuasiSeparatedSpace Y']
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g)
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (fAdj : pushforwardCohomologyIn f ⊣ a)
    (f'Adj : pushforwardCohomologyIn f' ⊣ a')
    (hTor : Scheme.TorIndependentOver (Over.mk f) (Over.mk g))
    (baseChangeIso :
      pushforwardCohomologyIn f ⋙ pullback g ≅ pullback g' ⋙ pushforwardCohomologyIn f')
    (h_baseChange : baseChangeIso.hom = map g' f' f g sq.toCommSq)
    (K : DerivedQCoh Y) :
    (map g' f' f g sq.toCommSq).app (a.obj K) ≫
        (pushforwardCohomologyIn f').map
          ((CategoryTheory.DerivedBaseChange.map fAdj f'Adj baseChangeIso.symm).app K) ≫
      f'Adj.counit.app ((pullback g).obj K) =
    (pullback g).map (fAdj.counit.app K) := sorry

/-- For a Tor-independent cartesian square of quasi-compact and quasi-separated schemes,
the adjunction units commute with the inverse mate of an explicitly chosen base-change
isomorphism and the corresponding canonical base-change map. -/
theorem unit_baseChange
    {X' X Y' Y : Scheme.{u}}
    [CompactSpace X'] [QuasiSeparatedSpace X']
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y'] [QuasiSeparatedSpace Y']
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (sq : IsPullback g' f' f g)
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (fAdj : pushforwardCohomologyIn f ⊣ a)
    (f'Adj : pushforwardCohomologyIn f' ⊣ a')
    (hTor : Scheme.TorIndependentOver (Over.mk f) (Over.mk g))
    (baseChangeIso :
      pushforwardCohomologyIn f ⋙ pullback g ≅
        pullback g' ⋙ pushforwardCohomologyIn f')
    (h_baseChange : baseChangeIso.hom = map g' f' f g sq.toCommSq) :
    (pullback g').leftUnitor.inv ≫
          Functor.whiskerRight fAdj.unit (pullback g') ≫
          (Functor.associator (pushforwardCohomologyIn f) a (pullback g')).hom ≫
          Functor.whiskerLeft (pushforwardCohomologyIn f)
            (CategoryTheory.DerivedBaseChange.map fAdj f'Adj baseChangeIso.symm) ≫
          (Functor.associator (pushforwardCohomologyIn f) (pullback g) a').inv ≫
        Functor.whiskerRight (map g' f' f g sq.toCommSq) a' =
      (pullback g').rightUnitor.inv ≫
          Functor.whiskerLeft (pullback g') f'Adj.unit ≫
        (Functor.associator (pullback g') (pushforwardCohomologyIn f') a').inv := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh.BaseChange
