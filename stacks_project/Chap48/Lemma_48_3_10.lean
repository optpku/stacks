/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.GlobalTrace
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u

/- Lemma 48.3.10: for a morphism `f : X ⟶ Y` of quasi-compact, quasi-separated schemes,
the sheafy trace induces an isomorphism from the global derived Hom of `L` into `a.obj K` to
the global derived Hom of derived pushforward of `L` into `K`. -/
@[stacks 0B6I] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.globalTraceMapIsIso :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [CompactSpace X] [QuasiSeparatedSpace X]
      [QuasiSeparatedSpace Y]
      [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.TensorDescends X.toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.IsLocalization X.toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends Y.toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.TensorDescends Y.toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.IsLocalization Y.toRingedSpace]
      [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
      [MonoidalClosed (RingedSpace.ModuleDerived Y.toRingedSpace)]
      [RingedSite.Hom.DerivedAdjunction.HasPair
        (RingedSpace.opensRingedSiteHom f.toShHom)]
      [CategoryTheory.Functor.Monoidal
        (RingedSpace.modulePullbackDerived f.toShHom)]
      [CompactSpace Y]
      (a : Scheme.DerivedQCoh Y ⥤ Scheme.DerivedQCoh X)
      (adj : Scheme.DerivedQCoh.pushforwardCohomologyIn f ⊣ a)
      (L : Scheme.DerivedQCoh X) (K : Scheme.DerivedQCoh Y),
      IsIso (Scheme.DerivedQCoh.globalTraceMap f a adj L K))
