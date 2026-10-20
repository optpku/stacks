/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap48.Lemma_48_8_2_Comparison
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.DerivedQCoh
open AlgebraicGeometry.RingedSpace.ModuleDerived.KFlat
open CategoryTheory.MonoidalCategory
open RingedSite.Hom.DerivedAdjunction

noncomputable section

universe u

/- Lemma 48.8.2: for a Tor-independent cartesian square of quasi-compact and
quasi-separated schemes, the tensor-duality comparison commutes with derived pullback
and the right-adjoint base-change map. -/
@[stacks 0B6P] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.pullbackTensorDualityMap_baseChange :
    ∀ {X' X Y' Y : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [CompactSpace X'] [QuasiSeparatedSpace X']
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y'] [QuasiSeparatedSpace Y']
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [HomotopyTensorDescends X'.toRingedSpace] [TensorDescends X'.toRingedSpace]
    [IsLocalization X'.toRingedSpace]
    [HomotopyTensorDescends X.toRingedSpace] [TensorDescends X.toRingedSpace]
    [IsLocalization X.toRingedSpace]
    [HomotopyTensorDescends Y'.toRingedSpace] [TensorDescends Y'.toRingedSpace]
    [IsLocalization Y'.toRingedSpace]
    [HomotopyTensorDescends Y.toRingedSpace] [TensorDescends Y.toRingedSpace]
    [IsLocalization Y.toRingedSpace]
    [HasPair (RingedSpace.opensRingedSiteHom f.toShHom)]
    [HasPair (RingedSpace.opensRingedSiteHom f'.toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived f'.toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived g'.toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived g.toShHom)]
    (sq : IsPullback g' f' f g)
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (a' : DerivedQCoh Y' ⥤ DerivedQCoh X')
    (fAdj : pushforwardCohomologyIn f ⊣ a)
    (f'Adj : pushforwardCohomologyIn f' ⊣ a')
    (hTor : Scheme.TorIndependentOver (Over.mk f) (Over.mk g))
    (K : DerivedQCoh Y),
    let dualBaseChangeIso :=
      @asIso _ _ _ _
        (BaseChange.rightMate g' f' f g sq.toCommSq a a' fAdj f'Adj)
        (BaseChange.rightMate_isIso_of_torIndependent
          g' f' f g sq a a' fAdj f'Adj hTor)
    CommSq
      ((pullback g').map (pullbackTensorDualityMap f a fAdj K))
      (pullbackTensorDualityBaseChangeMap
        g' f' f g sq.toCommSq a a' dualBaseChangeIso K)
      (rightAdjointBaseChangeMap g' g a a' dualBaseChangeIso K)
      (pullbackTensorDualityMap f' a' f'Adj ((pullback g).obj K)))
