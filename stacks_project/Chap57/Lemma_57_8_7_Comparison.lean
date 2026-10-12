/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.FourierMukai.RightAdjoint

open AlgebraicGeometry CategoryTheory
open RingedSpace.ModuleDerived.KFlat
open RingedSite.Hom.DerivedAdjunction
universe u

/- The canonical comparison retained at the historical import path. -/
#check (AlgebraicGeometry.Scheme.FourierMukai.homComparison :
  ∀ {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S]
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends
      (Limits.pullback g f).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends
      (Limits.pullback g f).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization
      (Limits.pullback g f).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends
      (Limits.pullback f g).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends
      (Limits.pullback f g).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization
      (Limits.pullback f g).toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends Y.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.TensorDescends Y.toRingedSpace]
    [RingedSpace.ModuleDerived.KFlat.IsLocalization Y.toRingedSpace]
    [RingedSite.Hom.DerivedAdjunction.HasPair
      (RingedSpace.opensRingedSiteHom (Limits.pullback.snd f g).toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived
      (Limits.pullbackSymmetry g f).inv.toShHom)]
    [Functor.Monoidal (RingedSpace.modulePullbackDerived
      (Limits.pullback.snd f g).toShHom)]
    (H : MonoidalClosed
      (RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace))
    (K : Scheme.DerivedQCoh (Limits.pullback f g))
    (hK : RingedSpace.ModuleDerived.IsPseudoCoherent K.obj)
    (a : Scheme.DerivedQCoh Y ⥤ Scheme.DerivedQCoh (Limits.pullback f g))
    (aAdjunction : Scheme.DerivedQCoh.pushforwardCohomologyIn
      (Limits.pullback.snd f g) ⊣ a),
    AlgebraicGeometry.Scheme.FourierMukai.homComparisonFamily f g H K hK a aAdjunction)
