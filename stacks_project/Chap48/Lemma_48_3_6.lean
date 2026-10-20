/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.SheafyTrace
public import stacks_project.Chap48.Lemma_48_3_1_Instances
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Lemma 48.3.6: the sheafy trace map for a chosen right adjoint to derived
quasicoherent pushforward becomes an isomorphism after applying `DQ_Y`. -/
@[stacks 0A9Q] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.coheratedSheafyTraceMapIsIso :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [CompactSpace X] [QuasiSeparatedSpace X]
      [CompactSpace Y] [QuasiSeparatedSpace Y]
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
      [Functor.Monoidal (RingedSpace.modulePullbackDerived f.toShHom)]
      (a : DerivedQCoh Y ⥤ DerivedQCoh X)
      (adj : pushforward f ⊣ a)
      (L : DerivedQCoh X) (K : DerivedQCoh Y),
      IsIso (AlgebraicGeometry.Scheme.DerivedQCoh.coheratedSheafyTraceMap f a adj L K))

end AlgebraicGeometry.Scheme.DerivedQCoh
