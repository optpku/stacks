/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.BaseChange
public import ReasLib.CategoryTheory.Adjunction.BaseChange

/-!
# Units and derived base change on algebraic spaces

The units of right adjoints to derived pushforward commute with canonical
Tor-independent base change and its inverse mate.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.BaseChange

/-- For a Tor-independent cartesian square of algebraic spaces, the adjunction units
commute with the canonical derived base-change map and the right mate of its inverse.
The equality compares the complete whiskered-unit paths as natural transformations. -/
theorem unit_baseChange
    {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g']
    (sq : IsPullback g' f' f g)
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (fAdj : pushforwardCohomologyIn f ⊣ a)
    (f'Adj : pushforwardCohomologyIn f' ⊣ a')
    (hTor : TorIndependentOver (Over.mk f) (Over.mk g)) :
    let baseChangeIso :=
      @asIso _ _ _ _ (map g' f' f g sq.toCommSq)
        (map_isIso_of_torIndependent g' f' f g sq hTor)
    (pullback g').leftUnitor.inv ≫
          Functor.whiskerRight fAdj.unit (pullback g') ≫
          (Functor.associator (pushforwardCohomologyIn f) a (pullback g')).hom ≫
          Functor.whiskerLeft (pushforwardCohomologyIn f)
            (CategoryTheory.DerivedBaseChange.map fAdj f'Adj baseChangeIso.symm) ≫
          (Functor.associator (pushforwardCohomologyIn f) (pullback g) a').inv ≫
        Functor.whiskerRight (map g' f' f g sq.toCommSq) a' =
      (pullback g').rightUnitor.inv ≫
          Functor.whiskerLeft (pullback g') f'Adj.unit ≫
        (Functor.associator (pullback g') (pushforwardCohomologyIn f') a').inv :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.BaseChange
